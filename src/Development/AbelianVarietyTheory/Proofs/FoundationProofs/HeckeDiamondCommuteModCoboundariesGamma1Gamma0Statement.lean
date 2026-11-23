module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCompMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGam
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraDecompositionCocycleStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTCoeffFormulaCommDistinctPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitCommDiamondOperatorOfMatrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorPreservesModularFormGamma1InterGamma0
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeriodMapEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0Level
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitCommDiamondOperatorOfMatriStatement

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeUOperatorExplicit_comm_diamondOperatorOfMatrix : ∀ (N l q : ℕ) (k d : ℤ) (ρ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → q ∣ N * l → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.uOp q (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.uOp q ⇑f) := by
  first | exact @GlobalTheory.Hk.uOp_dia_comm | exact GlobalTheory.Hk.uOp_dia_comm | (intros; apply GlobalTheory.Hk.uOp_dia_comm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRangeMulEq

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem sum_range_mul_eq (h : ℕ → ℂ) (q r : ℕ) :
    ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range q, h (j + q * i) = ∑ m ∈ Finset.range (q * r), h m := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.add_comm]

theorem im_div_pos (τ : ℍ) (j q : ℕ) (hq : 0 < q) : 0 < (((τ : ℂ) + j) / q).im := by
  rw [Complex.div_natCast_im]
  simp only [Complex.add_im, Complex.natCast_im, add_zero]
  exact div_pos τ.im_pos (by exact_mod_cast hq)

theorem uOp_uOp_eq (f : ℍ → ℂ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (τ : ℍ) :
    uOp a (uOp b f) τ =
      ((a : ℂ) * b)⁻¹ * ∑ m ∈ Finset.range (a * b), f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b))) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [uOp]
  rw [← sum_range_mul_eq (fun m : ℕ => f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b)))) a b]
  conv_rhs => rw [Finset.sum_comm]
  rw [mul_inv, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofComplex_apply_of_im_pos (im_div_pos τ j a ha)]
  congr 2
  push_cast
  field_simp
  ring

theorem uOp_comm (f : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    uOp q (uOp r f) = uOp r (uOp q f) := by
  funext τ
  rw [uOp_uOp_eq f q r hq hr, uOp_uOp_eq f r q hr hq, mul_comm (r : ℂ), Nat.mul_comm r q]

theorem sum_mul_mod (G : ℕ → ℂ) (q r : ℕ) (hq : 0 < q) (hc : Nat.Coprime q r) :
    ∑ j ∈ Finset.range q, G (r * j % q) = ∑ j ∈ Finset.range q, G j := by
  have hinj : Set.InjOn (fun j => r * j % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h1 : a ≡ b [MOD q] := Nat.ModEq.cancel_left_of_coprime hc hab
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  have himg : (Finset.range q).image (fun j => r * j % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨a, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image hinj, himg]

theorem per_ofComplex (g : ℍ → ℂ) (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) (z : ℂ) (hz : 0 < z.im) :
    g (ofComplex (z + 1)) = g (ofComplex z) := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  have h1 : ofComplex (z + 1) = (1 : ℝ) +ᵥ ofComplex z := by
    apply UpperHalfPlane.ext
    rw [coe_vadd, ofComplex_apply_of_im_pos hz1, ofComplex_apply_of_im_pos hz]
    push_cast
    ring
  rw [h1, hper]

theorem uOp_vOp (g : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hc : Nat.Coprime q r)
    (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) :
    uOp q (vOp r g) = vOp r (uOp q g) := by
  funext τ
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hw : 0 < ((r : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hr) τ.im_pos
  simp only [uOp, vOp]
  rw [ofComplex_apply_of_im_pos hw]
  congr 1
  set w : ℂ := (r : ℂ) * τ with hwdef
  set G : ℕ → ℂ := fun m => g (ofComplex ((w + m) / q)) with hG
  have hGq : ∀ m n : ℕ, G (m + q * n) = G m := by
    intro m n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih]
      simp only [hG]
      have hpos : 0 < ((w + ((m + q * n : ℕ) : ℂ)) / q).im := by
        rw [Complex.div_natCast_im]
        simp only [Complex.add_im, Complex.natCast_im, add_zero]
        exact div_pos hw (by exact_mod_cast hq)
      rw [← per_ofComplex g hper _ hpos]
      congr 2
      push_cast
      field_simp
      ring
  have hmod : ∀ m, G m = G (m % q) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m q]
    exact hGq _ _
  calc ∑ j ∈ Finset.range q, g (ofComplex ((r : ℂ) * ↑(ofComplex (((τ : ℂ) + j) / q))))
      = ∑ j ∈ Finset.range q, G (r * j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hG]
        rw [ofComplex_apply_of_im_pos (im_div_pos τ j q hq)]
        congr 2
        rw [hwdef]
        push_cast
        field_simp
    _ = ∑ j ∈ Finset.range q, G (r * j % q) := Finset.sum_congr rfl fun j _ => hmod _
    _ = ∑ j ∈ Finset.range q, G j := sum_mul_mod G q r hq hc
    _ = _ := rfl

theorem uOp_add (q : ℕ) (f g : ℍ → ℂ) : uOp q (f + g) = uOp q f + uOp q g := by
  funext τ
  simp [uOp, Finset.sum_add_distrib, mul_add]

theorem uOp_smul (q : ℕ) (c : ℂ) (f : ℍ → ℂ) : uOp q (c • f) = c • uOp q f := by
  funext τ
  simp [uOp, Finset.mul_sum, mul_left_comm]

theorem T_mem_lev (N l : ℕ) : ModularGroup.T ∈ lev N l := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp [ModularGroup.T]
  · rw [Gamma0_mem]
    simp [ModularGroup.T]

theorem uOp_heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    r.Prime → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l r σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.uOp q (GlobalTheory.Hk.heckeT k r σ ⇑f) = GlobalTheory.Hk.heckeT k r σ (GlobalTheory.Hk.uOp q ⇑f) := by
  intro N l q r k σ hN hl hq hqd hr hrd hσ f
  have hq0 : 0 < q := hq.pos
  have hr0 : 0 < r := hr.pos
  have hne : q ≠ r := fun h => hrd (h ▸ hqd)
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hne
  have hinv : ∀ γ ∈ lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ => by
    rw [SL_slash]; exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  have hper : ∀ τ : ℍ, ((⇑f) ∣[k] σ) ((1 : ℝ) +ᵥ τ) = ((⇑f) ∣[k] σ) τ := by
    intro τ
    have h1 : ((⇑f) ∣[k] σ) ∣[k] ModularGroup.T = (⇑f) ∣[k] σ := by
      have e : σ * ModularGroup.T = (σ * ModularGroup.T * σ⁻¹) * σ := by group
      rw [← SlashAction.slash_mul, e, SlashAction.slash_mul,
        hinv _ (isDia_conj_mem_lev N l r σ _ hσ (T_mem_lev N l))]
    have h2 := congr_fun h1 τ
    have hden : denom (ModularGroup.T : GL (Fin 2) ℝ) τ = 1 := by
      rw [denom]; simp [ModularGroup.coe_T]
    rw [SL_slash_apply, modular_T_smul] at h2
    simpa [hden] using h2
  have hd := GlobalTheory.T.heckeUOperatorExplicit_comm_diamondOperatorOfMatrix N l q k r σ hN hl hq hqd hσ f
  unfold GlobalTheory.Hk.dia at hd
  simp only [GlobalTheory.Hk.heckeT]
  rw [uOp_add, uOp_smul, uOp_comm _ q r hq0 hr0, uOp_vOp _ q r hq0 hr0 hcop hper, hd]

end GlobalTheory.Hk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDiamondCommuteModCoboundariesGamma1Gamma0

section

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Comm

open CongruenceSubgroup

theorem cj_sub {Γ : Type} (u v : Γ → ℂ[X]) : cj (u - v) = cj u - cj v := by
  funext γ
  simp [cj, Polynomial.map_sub]

theorem intCast_of_dvd {m n : ℕ} (h : m ∣ n) {x a : ℤ} (hx : ((x : ℤ) : ZMod n) = a) :
    ((x : ℤ) : ZMod m) = a := by
  have := congrArg (ZMod.castHom h (ZMod m)) hx
  simpa using this

theorem isDia_mul {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : GlobalTheory.Hk.IsDia N l d σ)
    (hτ : GlobalTheory.Hk.IsDia N l e τ) : GlobalTheory.Hk.IsDia N l (d * e) (σ * τ) := by
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h3, h4⟩ := hτ
  have h1' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using intCast_of_dvd (dvd_mul_right N l) (a := 0) (by simpa using h1)
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h3]
    ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1', h2, h4]
    ring

theorem gamma_le_lev (N l : ℕ) : Gamma (N * l) ≤ Lev N l := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  refine ⟨?_, ?_⟩
  · change γ ∈ Gamma1 N
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 1) (by simpa using h00)
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 1) (by simpa using h11)
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 0) (by simpa using h10)
  · change γ ∈ Gamma0 l
    rw [Gamma0_mem]
    simpa using intCast_of_dvd (dvd_mul_left l N) (a := 0) (by simpa using h10)

theorem comm_of_decomp {Γ : Subgroup SL(2, ℤ)} {w : ℕ} (A B : Module.End ℂ (Γ → ℂ[X]))
    (hA : ∀ z ∈ B1 Γ w, A z ∈ B1 Γ w) (hB : ∀ z ∈ B1 Γ w, B z ∈ B1 Γ w)
    (hAc : ∀ z, cj (A z) = A (cj z)) (hBc : ∀ z, cj (B z) = B (cj z))
    (x y b : Γ → ℂ[X]) (hx : A (B x) - B (A x) ∈ B1 Γ w) (hy : A (B y) - B (A y) ∈ B1 Γ w)
    (hb : b ∈ B1 Γ w) :
    A (B (x + cj y + b)) - B (A (x + cj y + b)) ∈ B1 Γ w := by
  have hcj : ∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w := (cj_mem_Z1_cj_mem_B1_per_smul Γ w).2.1
  have e : A (B (x + cj y + b)) - B (A (x + cj y + b)) =
      (A (B x) - B (A x)) + cj (A (B y) - B (A y)) + (A (B b) - B (A b)) := by
    simp only [cj_sub, hAc, hBc, map_add (f := _)]
    abel
  rw [e]
  exact add_mem (add_mem hx (hcj _ hy)) (sub_mem (hA _ (hB _ hb)) (hB _ (hA _ hb)))

theorem per_comm {Γ : Subgroup SL(2, ℤ)} {w : ℕ} {k : ℤ} (A B : Module.End ℂ (Γ → ℂ[X]))
    (FA FB : (ℍ → ℂ) → ℍ → ℂ)
    (hA : ∀ z ∈ B1 Γ w, A z ∈ B1 Γ w) (hB : ∀ z ∈ B1 Γ w, B z ∈ B1 Γ w)
    (mA : ∀ f : ModularForm Γ k, ∃ g : ModularForm Γ k, ⇑g = FA ⇑f)
    (mB : ∀ f : ModularForm Γ k, ∃ g : ModularForm Γ k, ⇑g = FB ⇑f)
    (eA : ∀ f : ModularForm Γ k, per Γ w (FA ⇑f) - A (per Γ w ⇑f) ∈ B1 Γ w)
    (eB : ∀ f : ModularForm Γ k, per Γ w (FB ⇑f) - B (per Γ w ⇑f) ∈ B1 Γ w)
    (hc : ∀ f : ModularForm Γ k, FA (FB ⇑f) = FB (FA ⇑f)) (f : ModularForm Γ k) :
    A (B (per Γ w ⇑f)) - B (A (per Γ w ⇑f)) ∈ B1 Γ w := by
  obtain ⟨g, hg⟩ := mB f
  obtain ⟨g', hg'⟩ := mA f
  have h1 := eB f
  have h2 := eA g
  have h3 := eA f
  have h4 := eB g'
  rw [hg] at h2
  rw [hg'] at h4
  have e : A (B (per Γ w ⇑f)) - B (A (per Γ w ⇑f)) =
      -A (per Γ w (FB ⇑f) - B (per Γ w ⇑f)) - (per Γ w (FA (FB ⇑f)) - A (per Γ w (FB ⇑f))) +
        (per Γ w (FB (FA ⇑f)) - B (per Γ w (FA ⇑f))) + B (per Γ w (FA ⇑f) - A (per Γ w ⇑f)) := by
    rw [hc f]
    simp only [map_sub]
    abel
  rw [e]
  exact add_mem (add_mem (sub_mem (neg_mem (hA _ h1)) h2) h4) (hB _ h3)

theorem heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → Odd k →
  ∀ (q q' : ℕ) (σ σ' τ τ' : SL(2, ℤ)) (d d' : ZMod N), q.Prime → ¬ q ∣ N * l → q'.Prime → ¬ q' ∣ N * l →
   IsDiam N l (q : ZMod N) σ → IsDiam N l (q' : ZMod N) σ' → IsDiam N l d τ → IsDiam N l d' τ' →
   ∀ z ∈ Z1 (Lev N l) (k - 2),
    TqZ (Lev N l) (k - 2) q σ (TqZ (Lev N l) (k - 2) q' σ' z) - TqZ (Lev N l) (k - 2) q' σ' (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (UlZ (Lev N l) (k - 2) l z) - UlZ (Lev N l) (k - 2) l (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    UlZ (Lev N l) (k - 2) l (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (UlZ (Lev N l) (k - 2) l z) ∈ B1 (Lev N l) (k - 2) ∧
    DdZ (Lev N l) (k - 2) τ (DdZ (Lev N l) (k - 2) τ' z) - DdZ (Lev N l) (k - 2) τ' (DdZ (Lev N l) (k - 2) τ z) ∈ B1 (Lev N l) (k - 2) := by
  intro N l k hN hl hlN hk hodd q q' σ σ' τ τ' d d' hq hqNl hq' hq'Nl hσ hσ' hτ hτ' z hz
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨bUl, bDd, bTq, bDia, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level N l hN hl hlN
  have eqv := fun f => GlobalTheory.HeckeFamilyMatrices.HeckeEqv.period_map_equivariant N l k hN hl hlN hk f

  have opT : ∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
      GlobalTheory.Hk.IsDia N l q σ ∧
      (∀ z ∈ B1 (Lev N l) (k - 2), TqZ (Lev N l) (k - 2) q σ z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (TqZ (Lev N l) (k - 2) q σ z) = TqZ (Lev N l) (k - 2) q σ (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = TqF (k : ℤ) q σ ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (TqF (k : ℤ) q σ ⇑f) - TqZ (Lev N l) (k - 2) q σ (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    intro q σ hq hqn hs
    have dq : GlobalTheory.Hk.IsDia N l q σ := (bDia N l q σ).1 (by rwa [Int.cast_natCast])
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) (Fin (q + 1)) (dg 1 q) (tqFam q σ)
      (by simp [dg, Matrix.det_fin_two, hq.pos]) (rT q σ hq hqn hs)
    refine ⟨dq, H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).1 q σ hq hqn hs⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.heckeT_modularForm N l q k σ hN0 hq hqn dq f
    exact ⟨g, hg.trans (bTq _ _ _ _ hq.pos).symm⟩

  have opU :
      (∀ z ∈ B1 (Lev N l) (k - 2), UlZ (Lev N l) (k - 2) l z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (UlZ (Lev N l) (k - 2) l z) = UlZ (Lev N l) (k - 2) l (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = UlF (k : ℤ) l ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (UlF (k : ℤ) l ⇑f) - UlZ (Lev N l) (k - 2) l (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) (Fin l) (dg 1 l) (ulFam l)
      (by simp [dg, Matrix.det_fin_two, hl.pos]) rU
    refine ⟨H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).2.1⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.uOp_modularForm N l l k hN0 hl0 hl (dvd_mul_left l N) f
    exact ⟨g, hg.trans (bUl _ _ _ hl0).symm⟩

  have opD : ∀ (d : ZMod N) (τ : SL(2, ℤ)), IsDiam N l d τ →
      GlobalTheory.Hk.IsDia N l (mat τ 1 1) τ ∧
      (∀ z ∈ B1 (Lev N l) (k - 2), DdZ (Lev N l) (k - 2) τ z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (DdZ (Lev N l) (k - 2) τ z) = DdZ (Lev N l) (k - 2) τ (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = DdF (k : ℤ) τ ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (DdF (k : ℤ) τ ⇑f) - DdZ (Lev N l) (k - 2) τ (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    intro d τ hs
    have dτ : GlobalTheory.Hk.IsDia N l (mat τ 1 1) τ := (bDia N l (mat τ 1 1) τ).1 ⟨hs.1, rfl⟩
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) Unit (mat τ) (fun _ => mat τ)
      (by simp [mat]) (rD d τ hs)
    refine ⟨dτ, H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).2.2 d τ hs⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.dia_modularForm N l k (mat τ 1 1) τ hN0 dτ f
    exact ⟨g, hg.trans (bDd _ _ _).symm⟩

  obtain ⟨f, h, hES⟩ := GlobalTheory.T.exists_eichlerShimura_decomposition_cocycle N (N * l) (Lev N l) k hN (Nat.mul_pos hN0 hl0)
    (gamma_le_lev N l) inf_le_left hodd hk z hz
  obtain ⟨b, hb, rfl⟩ : ∃ b ∈ B1 (Lev N l) (k - 2),
      z = per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b :=
    ⟨_, hES, by abel⟩
  have hh : ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = ⇑h := ⟨ModularFormClass.modularForm h, rfl⟩
  obtain ⟨hm, hhm⟩ := hh
  have pair : ∀ (A B : Module.End ℂ (Lev N l → ℂ[X])) (FA FB : (ℍ → ℂ) → ℍ → ℂ),
      (∀ z ∈ B1 (Lev N l) (k - 2), A z ∈ B1 (Lev N l) (k - 2)) ∧
        (∀ z, cj (A z) = A (cj z)) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = FA ⇑f) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ),
          per (Lev N l) (k - 2) (FA ⇑f) - A (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) →
      (∀ z ∈ B1 (Lev N l) (k - 2), B z ∈ B1 (Lev N l) (k - 2)) ∧
        (∀ z, cj (B z) = B (cj z)) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = FB ⇑f) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ),
          per (Lev N l) (k - 2) (FB ⇑f) - B (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) →
      (∀ f : ModularForm (Lev N l) (k : ℤ), FA (FB ⇑f) = FB (FA ⇑f)) →
      A (B (per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b)) -
        B (A (per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b)) ∈ B1 (Lev N l) (k - 2) := by
    rintro A B FA FB ⟨hA, hAc, mA, eA⟩ ⟨hB, hBc, mB, eB⟩ hc
    have hy := per_comm A B FA FB hA hB mA mB eA eB hc hm
    rw [hhm] at hy
    exact comm_of_decomp A B hA hB hAc hBc _ _ b (per_comm A B FA FB hA hB mA mB eA eB hc f) hy hb

  have eT : ∀ (q : ℕ) (σ : SL(2, ℤ)), 0 < q → ∀ g, TqF (k : ℤ) q σ g = GlobalTheory.Hk.heckeT k q σ g :=
    fun q σ hq g => bTq _ q σ g hq
  have eU : ∀ g, UlF (k : ℤ) l g = GlobalTheory.Hk.uOp l g := fun g => bUl _ l g hl0
  have eD : ∀ (τ : SL(2, ℤ)) g, DdF (k : ℤ) τ g = GlobalTheory.Hk.dia k τ g := fun τ g => bDd _ τ g
  obtain ⟨dq, oTq⟩ := opT q σ hq hqNl hσ
  obtain ⟨dq', oTq'⟩ := opT q' σ' hq' hq'Nl hσ'
  obtain ⟨dτ, oDτ⟩ := opD d τ hτ
  obtain ⟨dτ', oDτ'⟩ := opD d' τ' hτ'
  refine ⟨pair _ _ _ _ oTq oTq' ?_, pair _ _ _ _ oTq opU ?_, pair _ _ _ _ oTq oDτ ?_,
    pair _ _ _ _ opU oDτ ?_, pair _ _ _ _ oDτ oDτ' ?_⟩
  · intro f
    simp only [eT q σ hq.pos, eT q' σ' hq'.pos]
    exact GlobalTheory.Hk.heckeT_comm N l q q' k σ σ' hN0 hq hq' hqNl hq'Nl dq dq' f
  · intro f
    simp only [eT q σ hq.pos, eU]
    exact (GlobalTheory.Hk.uOp_heckeT_comm N l l q k σ hN0 hl0 hl (dvd_mul_left l N) hq hqNl dq f).symm
  · intro f
    simp only [eT q σ hq.pos, eD]
    exact GlobalTheory.Hk.heckeT_dia_comm N l q k (mat τ 1 1) σ τ hN0 hq hqNl dq dτ f
  · intro f
    simp only [eU, eD]
    exact GlobalTheory.Hk.uOp_dia_comm N l l k (mat τ 1 1) τ hN0 hl0 hl (dvd_mul_left l N) dτ f
  · intro f
    simp only [eD]
    exact (GlobalTheory.Hk.dia_mul N l k _ _ τ' τ (τ' * τ) hN0 dτ' dτ (isDia_mul dτ' dτ) f).trans
      (GlobalTheory.Hk.dia_mul N l k _ _ τ τ' (τ' * τ) hN0 dτ dτ'
        (by rw [mul_comm (mat τ 1 1)]; exact isDia_mul dτ' dτ) f).symm

end GlobalTheory.HeckeFamilyMatrices.Comm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDiamondCommuteModCoboundariesGamma1Gamma0Statement

section

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0 : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → Odd k →
  ∀ (q q' : ℕ) (σ σ' τ τ' : SL(2, ℤ)) (d d' : ZMod N), q.Prime → ¬ q ∣ N * l → q'.Prime → ¬ q' ∣ N * l →
   IsDiam N l (q : ZMod N) σ → IsDiam N l (q' : ZMod N) σ' → IsDiam N l d τ → IsDiam N l d' τ' →
   ∀ z ∈ Z1 (Lev N l) (k - 2),
    TqZ (Lev N l) (k - 2) q σ (TqZ (Lev N l) (k - 2) q' σ' z) - TqZ (Lev N l) (k - 2) q' σ' (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (UlZ (Lev N l) (k - 2) l z) - UlZ (Lev N l) (k - 2) l (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    UlZ (Lev N l) (k - 2) l (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (UlZ (Lev N l) (k - 2) l z) ∈ B1 (Lev N l) (k - 2) ∧
    DdZ (Lev N l) (k - 2) τ (DdZ (Lev N l) (k - 2) τ' z) - DdZ (Lev N l) (k - 2) τ' (DdZ (Lev N l) (k - 2) τ z) ∈ B1 (Lev N l) (k - 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt | exact GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt | (intros; apply GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt <;> assumption)
end
end

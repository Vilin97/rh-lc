module

public import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
public import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockOfNormalForm
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockValueOnRowsEqStatement
public import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
public import Mathlib.RingTheory.MvPowerSeries.Rename
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataMainTermNormalFormAndLevelOneStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SumEqOfIsHomogeneous
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MainTermImpliesRowHypothesis

section

@[expose] public section

open Formalism.L2.FormalSeriesBounds

noncomputable section

open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.MainToRows

variable {C : Type} [Field C]

theorem killCompl_subst {σ τ κ : Type} [Finite κ] (e : σ ↪ τ) (a : κ → MvPowerSeries τ C)
    (ha : ∀ k, constantCoeff (a k) = 0) (H : MvPowerSeries κ C) :
    killCompl e (subst a H) = subst (fun k => killCompl e (a k)) H := by
  have hc : ∀ k, constantCoeff (killCompl e (a k)) = 0 := fun k => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
      coeff_zero_eq_constantCoeff_apply, ha]
  ext x
  rw [coeff_killCompl, coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero hc)]
  refine finsum_congr fun d => ?_
  rw [← coeff_killCompl, map_finsuppProd]
  simp only [map_pow]

def eps {n0 n : ℕ} (hn : n0 ≤ n) : Fin n0 ⊕ Fin n0 ↪ Fin n0 ⊕ Fin n :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hn)

theorem kill_inl {n0 n : ℕ} (hn : n0 ≤ n) (c : Fin n0) :
    killCompl (eps hn) (X (Sum.inl c) : MvPowerSeries (Fin n0 ⊕ Fin n) C) = X (Sum.inl c) :=
  killCompl_X (e := eps hn) (Sum.inl c)

theorem kill_inr {n0 n : ℕ} (hn : n0 ≤ n) (c : Fin n0) :
    killCompl (eps hn) (X (Sum.inr (Fin.castLE hn c)) : MvPowerSeries (Fin n0 ⊕ Fin n) C) =
      X (Sum.inr c) :=
  killCompl_X (e := eps hn) (Sum.inr c)

theorem kill_inr_zero {n0 n : ℕ} (hn : n0 ≤ n) (b : Fin n) (hb : b ∉ Set.range (Fin.castLE hn)) :
    killCompl (eps hn) (X (Sum.inr b) : MvPowerSeries (Fin n0 ⊕ Fin n) C) = 0 := by
  refine killCompl_X_eq_zero ?_
  rintro ⟨x | x, hx⟩
  · simp [eps] at hx
  · exact hb ⟨x, by simpa [eps] using hx⟩

theorem sum_castLE {M : Type*} [AddCommMonoid M] {n0 n : ℕ} (hn : n0 ≤ n) (f : Fin n → M)
    (hf : ∀ b, b ∉ Set.range (Fin.castLE hn) → f b = 0) :
    ∑ b, f b = ∑ b : Fin n0, f (Fin.castLE hn b) :=
  (Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ f hf (fun _ => rfl)).symm

theorem kill_hPullW {I : Fin 2 → Type} [∀ g, Fintype (I g)] {n0 n : ℕ} (hn : n0 ≤ n)
    (H : MvPowerSeries (WV I) C) (e : Fin n0 → WV I → C) (e' : Fin n → WV I → C) :
    killCompl (eps hn) (hPullW H e e') = hPullW H e (fun b => e' (Fin.castLE hn b)) := by
  unfold hPullW
  rw [killCompl_subst _ _ (fun k => by simp)]
  congr 1
  funext w

  rw [map_add (f := _), map_sum, map_sum, sum_castLE hn (fun b => killCompl (eps hn) (e' b w • X (Sum.inr b)))]
  · simp only [map_smul, kill_inl, kill_inr]
  · intro b hb
    rw [map_smul, kill_inr_zero hn b hb, smul_zero]

theorem kill_mainM (V : VF C) (i : ℕ) {n0 n : ℕ} (hn : n0 ≤ n) (Φ : Fin n → Fin n0 → C) :
    killCompl (eps hn) (mainM V i Φ) = mainM V i (fun b c => Φ (Fin.castLE hn b) c) := by
  unfold mainM

  rw [map_smul, map_sum, sum_castLE hn]

  · simp only [map_sum, map_smul, map_mul, map_pow, kill_inl, kill_inr]
  · intro b hb

    simp only [map_sum, map_smul, map_mul, kill_inr_zero hn b hb, mul_zero, smul_zero,
    Finset.sum_const_zero]

theorem sum_inl_eps {n0 n : ℕ} (hn : n0 ≤ n) (μ : Fin n0 ⊕ Fin n0 →₀ ℕ) :
    ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inl c) = ∑ c, μ (Sum.inl c) :=
  Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (eps hn) μ (Sum.inl c)

theorem sum_inr_eps {n0 n : ℕ} (hn : n0 ≤ n) (μ : Fin n0 ⊕ Fin n0 →₀ ℕ) :
    ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inr c) = ∑ c, μ (Sum.inr c) := by
  rw [sum_castLE hn]
  · exact Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (eps hn) μ (Sum.inr c)
  · intro b hb
    refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
    rintro ⟨x | x, hx⟩
    · simp [eps] at hx
    · exact hb ⟨x, by simpa [eps] using hx⟩

def rowE {n0 : ℕ} (ρ : Fin n0) : Fin n0 ⊕ Fin n0 ↪ PVar n0 :=
  Function.Embedding.sumMap (Function.Embedding.sectR ρ (Fin n0)) (Function.Embedding.sectR ρ (Fin n0))

theorem hRows_eq (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) :
    hRows n0 H = ∑ ρ : Fin n0, rename (rowE ρ) H := by
  unfold hRows
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [rename_eq_subst]
  congr 1
  funext x
  rcases x with x | x <;> rfl

theorem coeff_row {n0 : ℕ} (ρ : Fin n0) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) (m : PVar n0 →₀ ℕ) :
    coeff m (rename (rowE ρ) H) = 0 ∨ ∃ μ : Fin n0 ⊕ Fin n0 →₀ ℕ,
      coeff m (rename (rowE ρ) H) = coeff μ H ∧ degL m = ∑ c, μ (Sum.inl c) ∧
        degR m = ∑ c, μ (Sum.inr c) ∧ ∀ x ∈ m.support, rowOf x = ρ := by
  by_cases h : m ∈ Set.range (Finsupp.mapDomain (rowE ρ))
  · obtain ⟨μ, rfl⟩ := h
    rw [← Finsupp.embDomain_eq_mapDomain]
    have hout : ∀ x : PVar n0, rowOf x ≠ ρ → Finsupp.embDomain (rowE ρ) μ x = 0 := by
      intro x hx
      refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
      rintro ⟨y | y, rfl⟩ <;> exact hx rfl
    refine Or.inr ⟨μ, coeff_embDomain_rename _ _ _, ?_, ?_, ?_⟩
    · unfold degL
      rw [Finset.sum_eq_single ρ]
      · exact Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (rowE ρ) μ (Sum.inl c)
      · exact fun b _ hb => Finset.sum_eq_zero fun c _ => hout _ hb
      · simp
    · unfold degR
      rw [Finset.sum_eq_single ρ]
      · exact Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (rowE ρ) μ (Sum.inr c)
      · exact fun b _ hb => Finset.sum_eq_zero fun c _ => hout _ hb
      · simp
    · intro x hx
      by_contra hne
      exact (Finsupp.mem_support_iff.1 hx) (hout x hne)
  · exact Or.inl (coeff_rename_eq_zero _ _ h)

theorem le_add_iff (w r : ℝ) (t : WithTop ℝ) :
    (w : WithTop ℝ) ≤ t + (r : WithTop ℝ) ↔ ((w - r : ℝ) : WithTop ℝ) ≤ t := by
  induction t with
  | top => simp
  | coe t => rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]

theorem rows_main (V : VF C) (i n0 : ℕ) :
    ∑ ρ : Fin n0, rename (rowE ρ) (mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0)) =
      -((V.l : C) ^ (expE V.l i))⁻¹ • (∑ b : Fin n0, ∑ c : Fin n0,
        (X (Sum.inl (b, c)) ^ (V.l ^ i) * X (Sum.inr (b, c)) : MvPowerSeries (PVar n0) C)) := by
  unfold mainM
  refine Eq.trans (Finset.sum_congr rfl fun ρ _ => ?_) (Finset.smul_sum).symm

  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_smul, map_sum,
  map_mul, map_pow, rename_X, neg_smul, one_smul, map_neg, Finset.sum_neg_distrib, smul_neg]
  rfl

end GlobalTheory.MainToRows


open GlobalTheory.MainToRows in
theorem GlobalTheory.mainTerm_to_rowHypothesis :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
      [∀ g, Fintype (J g)] (X : RowData C V d I J), X.MtoHM := by
  intro C _ V d _ I J _ _ X g a i U U' n0 e v' Φ hM hn
  obtain ⟨-, -, -, -, -, hΦ, hwt, hax⟩ := hM
  set H := X.hGood g a i hn e v' - mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0)
    with hH
  have hkill : H = killCompl (eps hn) (X.hM g a i e v' - mainM V i Φ) := by
    rw [hH, map_sub, kill_mainM]
    unfold RowData.hGood RowData.hM
    rw [kill_hPullW]
    congr 2
    funext b c
    rw [hΦ _ c (by simp)]
    simp [Fin.ext_iff]
  have hco : ∀ μ, coeff μ H = coeff (Finsupp.embDomain (eps hn) μ) (X.hM g a i e v' - mainM V i Φ) :=
    fun μ => by rw [hkill, coeff_killCompl]
  have h1 : X.restrictedCurveSystemSeries g a i hn e v' = ∑ ρ : Fin n0, rename (rowE ρ) H := hRows_eq _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, hRows_eq, hP, ← rows_main, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← map_add (f := _), hH, add_sub_cancel]
  · intro m

    rw [h1, le_add_iff, map_sum]
    refine V.v.map_le_sum fun ρ _ => ?_
    rcases coeff_row ρ H m with h | ⟨μ, h, hL, hR, -⟩
    · rw [h, V.v.map_zero]; exact le_top
    · rw [h, hco, ← le_add_iff, hL, hR, ← sum_inl_eps hn, ← sum_inr_eps hn]
      exact hwt _
  · intro m hm

    rw [h1, map_sum] at hm
    obtain ⟨ρ, -, hρ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rcases coeff_row ρ H m with h | ⟨μ, h, -, hR, -⟩
    · exact absurd h hρ
    · rw [h, hco] at hρ
      by_contra hlt
      refine hρ (hax _ ?_)
      have h0 : ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inr c) = 0 := by
        rw [sum_inr_eps, ← hR]; omega
      exact fun b => (Finset.sum_eq_zero_iff.1 h0) b (Finset.mem_univ b)
  · intro hi hP
    subst hi
    refine ⟨fun ρ => rename (rowE ρ) H, h1, fun ρ m hm => ?_, fun ρ m hl hr => ?_⟩
    · rcases coeff_row ρ H m with h | ⟨μ, -, -, -, h⟩
      · exact absurd h hm
      · exact h
    · rcases coeff_row ρ H m with h | ⟨μ, h, hL, hR, -⟩
      · rw [h, V.v.map_zero]; exact le_top
      · rw [h, hco]
        exact hP _ (by rw [sum_inl_eps, ← hL]; exact hl) (by rw [sum_inr_eps, ← hR]; exact hr)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MainTermImpliesRowHypothesisStatement

section

@[expose] public section

open Formalism.L2.FormalSeriesBounds

theorem _root_.GlobalTheory.T.mainTerm_implies_rowHypothesis : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.MtoHM := by
  first | exact @GlobalTheory.mainTerm_to_rowHypothesis | exact GlobalTheory.mainTerm_to_rowHypothesis | (intros; apply GlobalTheory.mainTerm_to_rowHypothesis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttained

section

@[expose] public section

noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.MinorShiftJet

variable {K : Type} [Field K] {V : VF K} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem big_shift (X : RowData K V d I J) (h : X.Alt) {g : Fin 2} {a : ZMod d} (ha : X.big g a) {i : ℕ}
    (hi : Odd i) : X.big (1 - g) (a + (i : ZMod d)) := by
  have hpar : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    rw [ZMod.val_add, ZMod.val_natCast]
    obtain ⟨r, hr⟩ := h.1
    have h2 : 2 ∣ d := ⟨r, by omega⟩
    rw [Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2, Nat.add_mod, Nat.mod_mod_of_dvd _ h2,
      Nat.odd_iff.1 hi]
    omega
  rw [X.big_compl]
  have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
  fin_cases g
  · simp only [Fin.zero_eta] at ha ⊢
    rw [h.2] at ha ⊢
    rw [hpar]; exact fun h' => h' ha
  · simp only [Fin.mk_one] at ha ⊢
    rw [h1, h.2] at ha ⊢
    rw [hpar]; exact fun h' => h' ha

omit [∀ g, Fintype (I g)] in
theorem rename_minor {n N : ℕ} (hN : n ≤ N) (g : Fin 2) (en : Fin N → I g) :
    MvPolynomial.rename (fun x : Fin n × Fin N => (x.1, (⟨g, en x.2⟩ : WV I))) (minorK K n N n) =
      letterDet K g fun c => en (Fin.castLE hN c) := by
  rw [minorK, dite_eq_left ⟨le_rfl, hN⟩, AlgHom.map_det, letterDet]
  congr 1
  refine Matrix.ext fun b c => ?_
  simp

theorem satIn_single (X : RowData K V d I J) (g : Fin 2) (a : ZMod d) {N : ℕ} (p : Fin N → I g)
    (hp : Function.Injective p) (hty : ∀ c, (X.G g).ty (Sum.inl (p c)) = a) :
    X.SatIn g a fun b x => if x = p b then 1 else 0 := by
  have h01 : ∀ (P : Prop) [Decidable P], V.Ge 0 (if P then (1 : K) else 0) := by
    intro P _; split_ifs
    exacts [VF.Ge.one, VF.Ge.zero _]
  refine ⟨⟨fun c x => h01 _, fun x c => if x = p c then 1 else 0, fun x c => h01 _, fun c c' => ?_⟩,
    fun c x hx => if_neg fun h => hx (by rw [h, hty])⟩
  simp [hp.eq_iff, eq_comm]

theorem cc_mvExp' {σ : Type} (x : MvPowerSeries σ K) : constantCoeff (mvExp x) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  change ∑ j ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), coeff 0 (x ^ j) / (j.factorial : K) = 1
  simp

theorem jetAt0_one' {σ : Type} (G : MvPowerSeries σ K) : jetAt0 1 G = constantCoeff G := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', jetAt0_monomial]
  simp [mfact]

theorem mono_resι_var {l i n0 n : ℕ} (hl : 5 ≤ l) (hn : n0 ≤ n) : S0 l i n0 ≤ S0 l i n := by
  unfold S0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ Real.logb l ((n0 : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith [Nat.cast_nonneg (α := ℝ) n0])
  have h1 : Real.logb l ((n0 : ℝ) + 1) ≤ Real.logb l ((n : ℝ) + 1) :=
    Real.logb_le_logb_of_le hl1 (by positivity) (by linarith)
  refine Nat.ceil_mono ?_
  gcongr

theorem sum_positive_of_five_le {l i n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) : 0 < S0 l i n := by
  unfold S0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ Real.logb l ((n : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith)
  refine Nat.ceil_pos.2 ?_
  positivity

theorem window_letterDet (X : RowData K V d I J) (hA : X.Alt) (hl : 5 ≤ V.l) (hn1 : 1 ≤ X.n)
    (g : Fin 2) (a : ZMod d) (ha : X.big g a) (i : ℕ) (hi : Odd i) (hid : i < d)
    (p : Fin X.n → I g) (p' : Fin X.n → I (1 - g)) (hp : Function.Injective p) (hp' : Function.Injective p')
    (hty : ∀ c, (X.G g).ty (Sum.inl (p c)) = a)
    (hty' : ∀ c, (X.G (1 - g)).ty (Sum.inl (p' c)) = a + (i : ZMod d)) :
    Windows (S0 V.l i X.n) {y | ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) K),
      (∀ g, (S g).IsT (t g)) ∧ ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (letterDet K g p ^ (V.l ^ i * y) * letterDet K (1 - g) p' ^ y)
          (fun _ => some (g, a, a + (i : ZMod d))) gr) ≤ ((blockBd V.l X.n X.m i y : ℝ) : WithTop ℝ)} := by
  have := X.charZero
  obtain ⟨n0, e, v', Φ, hM, -⟩ := (GlobalTheory.T.rowData_mainTerm_normalForm_and_levelOne K V d I J X).1 hA hl g a ha i hi hid _ _
    (satIn_single X g a p hp hty) (satIn_single X (1 - g) _ p' hp' hty')
  have hn : n0 ≤ X.n := hM.1.2
  obtain ⟨hR, hH1, hH2, -⟩ := GlobalTheory.T.mainTerm_implies_rowHypothesis K V d I J X g a i _ _ n0 e v' Φ hM hn
  obtain ⟨S, t, hSt, hr, tt, tt', hB, hy⟩ :=
    block_of_normal_form X g a i p p' hp hp' n0 e v' Φ hM hn _ hR
  have hrank : X.n - n0 ≤ (i + 1) * X.m := by
    have h1 := hM.1.1
    have h2 : (i + 1) * X.m = (i + 1) * X.j' + X.j + i * X.j := by unfold RowData.m; ring
    omega
  have hgood : ∀ y : ℕ, V.v (jetAt0 (detL K X.n ^ (V.l ^ i * y) * detR K X.n ^ y)
      (BiF V.l i n0 X.n y hr tt tt')) ≤ (((bdP V.l i X.n X.n y + ((i : ℝ) + 1) * X.m * ((V.l : ℝ) ^ i + 1) * y /
        ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ) ∨ y = 0 →
      ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (letterDet K g p ^ (V.l ^ i * y) * letterDet K (1 - g) p' ^ y)
          (fun _ => some (g, a, a + (i : ZMod d))) gr) ≤ ((blockBd V.l X.n X.m i y : ℝ) : WithTop ℝ) := by
    intro y h
    obtain ⟨gr, hgr, hv⟩ := hy y
    refine ⟨gr, hgr, hv.trans ?_⟩
    by_cases h0 : y = 0
    · subst h0
      simp only [blockBd, if_true, mul_zero, pow_zero, mul_one, jetAt0_one', BiF, ite_self, one_mul, map_prod,
        cc_mvExp', Finset.prod_const_one, V.v.map_one]
      rfl
    · rw [blockBd, if_neg h0]
      exact h.resolve_right h0
  refine ⟨⟨S, t, hSt, hgood 0 (Or.inr rfl)⟩, fun Y0 => ?_⟩
  rcases Nat.eq_zero_or_pos n0 with h0 | h0
  · subst h0
    refine ⟨Y0, ⟨S, t, hSt, hgood Y0 (Or.inl ?_)⟩, le_rfl, Nat.lt_add_of_pos_right (sum_positive_of_five_le hl hn1)⟩
    have hl1 : (1 : ℝ) < V.l := by exact_mod_cast (by omega : 1 < V.l)
    rw [GlobalTheory.T.blockValue_on_rows_eq K V.l i 0 X.n hn hr tt tt' _ hB Y0]
    refine (GlobalTheory.OddBlock.content_and_window.1 K V.v V.l V.l_prime hl V.v_l i X.n 0 Y0 hi hn1 hn _ ?_).trans ?_
    · have : LamP K V.l i 0 (X.restrictedCurveSystemSeries g a i hn e v') Y0 = 1 := by
        simp [LamP, detL, detR, jetAt0_one', cc_mvExp']
      rw [this, V.v.map_one]
      have hn' : (1 : ℝ) ≤ X.n := by exact_mod_cast hn1
      have h0 : 0 ≤ Real.logb V.l (X.n : ℝ) := Real.logb_nonneg hl1 hn'
      have : 0 ≤ bdP V.l i 0 X.n Y0 := by
        simp only [bdP, Nat.cast_zero, zero_mul, zero_add]; positivity
      exact_mod_cast this
    · rw [WithTop.coe_le_coe]
      have h3 : ((X.n : ℝ) - ((0 : ℕ) : ℝ)) ≤ ((i : ℝ) + 1) * X.m := by
        rw [Nat.cast_zero, sub_zero]; exact_mod_cast hrank
      have : (0 : ℝ) < (V.l : ℝ) - 1 := by linarith
      gcongr
  · obtain ⟨y, h1, h2, h3⟩ := GlobalTheory.OddBlock.content_and_window.2 K V.v V.l V.l_prime hl V.v_l i hi n0 X.n X.m hn h0 hrank hr tt tt' _
      hB hH1 hH2 Y0
    exact ⟨y, ⟨S, t, hSt, hgood y (Or.inl h3)⟩, h1, h2.trans_le (Nat.add_le_add_left (mono_resι_var hl hn) _)⟩

end GlobalTheory.MinorShiftJet

namespace GlobalTheory

open MinorShiftJet

theorem oddBlock_supply : BiSupply ∧ RF.BiSupply := by
  constructor
  · intro K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid
    have h1 : X.n ≤ X.rk g a := (Nat.le_add_right _ _).trans (X.rk_big g a ha).ge
    have h2 : X.n ≤ X.rk (1 - g) (a + (i : ZMod d)) :=
      (Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge
    have key := window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c))
      (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c))
      ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2))
      (fun c => F.en_ty _ _ _) (fun c => F.en_ty _ _ _)
    rw [← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))] at key
    exact key
  · intro K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid
    have h1 : X.n ≤ X.rkF g a := (Nat.le_add_right _ _).trans (X.rk_big g a ha).ge
    have h2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d)) :=
      (Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge
    have key := window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c))
      (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c))
      ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2))
      (fun c => F.en_ty _ _ _) (fun c => F.en_ty _ _ _)
    rw [← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))] at key
    exact key

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttainedStatement

section

@[expose] public section

open Formalism.L2.FormalSeriesBounds

theorem _root_.GlobalTheory.T.oddLevelBlock_bound_attained : BiSupply ∧ RF.BiSupply := by
  first | exact @GlobalTheory.oddBlock_supply | exact GlobalTheory.oddBlock_supply | (intros; apply GlobalTheory.oddBlock_supply <;> assumption)
end
end

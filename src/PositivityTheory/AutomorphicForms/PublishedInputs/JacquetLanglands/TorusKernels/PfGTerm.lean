module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.PiTensorProduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ValuationDetCongruenceSubgroupEqOne
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementE

section

@[expose] public section

theorem UpperTheory.Reformulated.B.ProdSubProdLeOfFactorsClose.main.{u_1} :
    ∀ {ι : Type u_1} (ν : Valuation ℂ NNReal) (s : Finset ι) (f g : ι → ℂ) (m : NNReal),
      (∀ i ∈ s, (ν : ℂ → NNReal) (f i) ≤ (1 : NNReal)) →
        (∀ i ∈ s, (ν : ℂ → NNReal) (g i) ≤ (1 : NNReal)) →
          (∀ i ∈ s, (ν : ℂ → NNReal) (f i - g i) ≤ m) →
            (ν : ℂ → NNReal) (∏ i ∈ s, f i) ≤ (1 : NNReal) ∧
              (ν : ℂ → NNReal) (∏ i ∈ s, g i) ≤ (1 : NNReal) ∧ (ν : ℂ → NNReal) (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ m := by
  classical
  intro ι ν s f g m
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ _
    simp
  | insert a s ha ih =>
    intro hf hg hfg
    obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    have fa := hf a (Finset.mem_insert_self a s)
    have ga := hg a (Finset.mem_insert_self a s)
    have fga := hfg a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul]
      calc ν (f a) * ν (∏ i ∈ s, f i) ≤ 1 * 1 := mul_le_mul' fa h1
        _ = 1 := one_mul 1
    · rw [map_mul]
      calc ν (g a) * ν (∏ i ∈ s, g i) ≤ 1 * 1 := mul_le_mul' ga h2
        _ = 1 := one_mul 1
    · have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
          = f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
      rw [e]
      refine le_trans (Valuation.map_add ν _ _) (max_le ?_ ?_)
      · rw [map_mul]
        calc ν (f a) * ν (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ 1 * m := mul_le_mul' fa h3
          _ = m := one_mul m
      · rw [map_mul]
        calc ν (f a - g a) * ν (∏ i ∈ s, g i) ≤ m * 1 := mul_le_mul' fga h2
          _ = m := mul_one m
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ValNatCastLe

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.adelicTermLemmas

theorem ch_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (n : ℕ) :
    f (ch a b n) = ch (f a) (f b) n := by
  have key : ∀ n, f (ch a b n) = ch (f a) (f b) n ∧ f (ch a b (n + 1)) = ch (f a) (f b) (n + 1) := by
    intro n
    induction n with
    | zero => simp [ch]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [ch, map_sub, map_mul, ih.1, ih.2]
  exact (key n).1

theorem ch_hom {R : Type*} [CommRing R] (s τ δ : R) (n : ℕ) :
    ch (s * τ) (s ^ 2 * δ) (n + 1) = s ^ n * ch τ δ (n + 1) := by
  have key : ∀ n, ch (s * τ) (s ^ 2 * δ) (n + 1) = s ^ n * ch τ δ (n + 1) ∧
      ch (s * τ) (s ^ 2 * δ) (n + 2) = s ^ (n + 1) * ch τ δ (n + 2) := by
    intro n
    induction n with
    | zero => simp [ch]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e : ch (s * τ) (s ^ 2 * δ) (n + 1 + 2) =
          s * τ * ch (s * τ) (s ^ 2 * δ) (n + 2) - s ^ 2 * δ * ch (s * τ) (s ^ 2 * δ) (n + 1) := rfl
      have e' : ch τ δ (n + 1 + 2) = τ * ch τ δ (n + 2) - δ * ch τ δ (n + 1) := rfl
      rw [e, e', ih.1, ih.2]
      ring
  exact (key n).1

theorem val_prod_sub {ι : Type*} (ν : Valuation ℂ ℝ≥0) (s : Finset ι) (f g : ι → ℂ) (m : ℝ≥0)
    (hf : ∀ i ∈ s, ν (f i) ≤ 1) (hg : ∀ i ∈ s, ν (g i) ≤ 1) (hfg : ∀ i ∈ s, ν (f i - g i) ≤ m) :
    ν (∏ i ∈ s, f i) ≤ 1 ∧ ν (∏ i ∈ s, g i) ≤ 1 ∧ ν (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ m :=
  _root_.UpperTheory.Reformulated.B.ProdSubProdLeOfFactorsClose.main ν s f g m hf hg hfg

open Classical in
theorem nz_prod {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (k₀ : ℕ)
    (t : InfinitePlace F → ℕ) (W : List (Pl F)) :
    (W.map (nz D k₀ t)).prod =
      (W.map fun w => ((((normV w : ℝ) ^ ((k₀ : ℝ) / 2 - 1) : ℝ)) : ℂ)).prod * ∏ v, (l : ℂ) ^ (t v * W.count (D.pl v)) := by
  induction W with
  | nil => simp
  | cons w W ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]
    have e : ∀ v, (l : ℂ) ^ (t v * (w :: W).count (D.pl v)) =
        (if D.pl v = w then (l : ℂ) ^ t v else 1) * (l : ℂ) ^ (t v * W.count (D.pl v)) := by
      intro v
      rw [List.count_cons]
      by_cases h : D.pl v = w
      · subst h
        rw [if_pos rfl]
        simp [mul_add, pow_add]
        try ring
      · have h' : ¬ (w == D.pl v) = true := by
          rw [beq_iff_eq]; exact fun e => h e.symm
        simp [h, h']
    simp only [e, Finset.prod_mul_distrib, nz]
    ring

theorem local_cong (ν : Valuation ℂ ℝ≥0) (hG : GCh) (τ δ U : ℂ) (m : ℝ≥0) (k₀ t : ℕ) (hk : 2 ≤ k₀) (hτ : ν τ ≤ 1)
    (hδ1 : ν δ ≤ 1) (hδ : ν δ ≤ m) (hτt : ν (τ ^ (2 * t) - 1) ≤ m) (hU1 : ν U ≤ 1) (hU : ν (U ^ t - 1) ≤ m) :
    ν (ch τ δ (k₀ - 1)) ≤ 1 ∧ ν (ch τ δ (k₀ + 2 * t - 1) * U ^ t) ≤ 1 ∧
      ν (ch τ δ (k₀ - 1) - ch τ δ (k₀ + 2 * t - 1) * U ^ t) ≤ m := by
  obtain ⟨n, rfl⟩ : ∃ n, k₀ = n + 2 := ⟨k₀ - 2, by omega⟩
  have e0 : n + 2 - 1 = n + 1 := by omega
  have e1 : n + 2 + 2 * t - 1 = (n + 2 * t) + 1 := by omega
  rw [e0, e1]
  obtain ⟨A1, A2⟩ := hG ν τ δ hτ hδ1 n
  obtain ⟨B1, B2⟩ := hG ν τ δ hτ hδ1 (n + 2 * t)
  have hUt : ν (U ^ t) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ (by positivity) hU1
  refine ⟨A1, ?_, ?_⟩
  · rw [map_mul]; exact mul_le_one' B1 hUt
  · have e : ch τ δ (n + 1) - ch τ δ (n + 2 * t + 1) * U ^ t =
        (ch τ δ (n + 1) - τ ^ n) + (τ ^ n * (1 - τ ^ (2 * t))) + (τ ^ (n + 2 * t) - ch τ δ (n + 2 * t + 1)) +
          ch τ δ (n + 2 * t + 1) * (1 - U ^ t) := by ring
    rw [e]
    have hτn : ν (τ ^ n) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ (by positivity) hτ
    refine ν.map_add_le (ν.map_add_le (ν.map_add_le (A2.trans hδ) ?_) ?_) ?_
    · rw [map_mul, ν.map_sub_swap]
      exact (mul_le_of_le_one_left (by positivity) hτn).trans hτt
    · rw [ν.map_sub_swap]; exact B2.trans hδ
    · rw [map_mul, ν.map_sub_swap]
      exact (mul_le_of_le_one_left (by positivity) B1).trans hU

end UpperTheory.Esk.adelicTermLemmas
end
end
end

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfGTerm

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.adelicTermLemmas

theorem term_v (k₀ t' cnt : ℕ) (hk : 2 ≤ k₀) (s τ δ U L : ℂ) (hs : s ≠ 0) (hδ : δ ≠ 0) (hδU : δ * U = L ^ cnt) (d tr : ℝ)
    (hd : 0 < d) (htr : (tr : ℂ) = s * τ) (hdet : (d : ℂ) = s ^ 2 * δ) :
    L ^ (t' * cnt) * -(((ch tr d (k₀ + 2 * t' - 1) * d ^ (1 - ((k₀ + 2 * t' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) =
      (s ^ (k₀ - 2) * ((d ^ (1 - (k₀ : ℝ) / 2) : ℝ) : ℂ)) * -(ch τ δ (k₀ + 2 * t' - 1) * U ^ t') := by
  have e1 : ((ch tr d (k₀ + 2 * t' - 1) : ℝ) : ℂ) = s ^ (k₀ - 2 + 2 * t') * ch τ δ (k₀ + 2 * t' - 1) := by
    have h := ch_map Complex.ofRealHom tr d (k₀ + 2 * t' - 1)
    simp only [Complex.ofRealHom_eq_coe] at h
    rw [h, htr, hdet]
    have hk' : k₀ + 2 * t' - 1 = (k₀ - 2 + 2 * t') + 1 := by omega
    rw [hk', ch_hom]
  have e2 : ((d ^ (1 - ((k₀ + 2 * t' : ℕ) : ℝ) / 2) : ℝ) : ℂ) = ((d ^ (1 - (k₀ : ℝ) / 2) : ℝ) : ℂ) * ((s ^ 2 * δ) ^ t')⁻¹ := by
    have h : (1 - ((k₀ + 2 * t' : ℕ) : ℝ) / 2) = (1 - (k₀ : ℝ) / 2) + (-(t' : ℝ)) := by push_cast; ring
    rw [h, Real.rpow_add hd, Real.rpow_neg hd.le, Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_pow, hdet]
  rw [Complex.ofReal_mul, e1, e2, mul_comm t' cnt, pow_mul, ← hδU, pow_add, mul_pow, mul_pow, ← pow_mul]
  field_simp

theorem list_prod_ofReal {α : Type*} (W : List α) (f : α → ℝ) : (W.map fun w => ((f w : ℝ) : ℂ)).prod = (((W.map f).prod : ℝ) : ℂ) := by
  induction W with
  | nil => simp
  | cons w W ih => simp [ih]

end UpperTheory.Esk.adelicTermLemmas

open UpperTheory.Esk.adelicTermLemmas Classical in
theorem UpperTheory.Esk.pf_GTerm : UpperTheory.Esk.GCh → UpperTheory.Esk.GUnit → UpperTheory.Esk.GMod → UpperTheory.Esk.GTerm := by
  intro hG hU hMod F _ _ _ l _ ι D c χ hc k₀ hk₀ N t ht W r hr hW n a hR γ x i hell hmem
  obtain ⟨k, hk, z, hkz⟩ := hc_decomp hmem
  have hrel1 : jF F γ * x * (k * zc F z) = x * a i := by rw [← hkz]; group
  have hrel2 : jF F γ = x * (a i * k⁻¹ * zc F z⁻¹) * x⁻¹ := by
    have hcz : k⁻¹ * zc F z⁻¹ = zc F z⁻¹ * k⁻¹ := Subgroup.mem_center_iff.1 (zc_center z⁻¹) k⁻¹
    have e : jF F γ = x * a i * (k * zc F z)⁻¹ * x⁻¹ := by rw [← hrel1]; group
    rw [e, mul_inv_rev, ← map_inv, ← hcz]
    simp only [mul_assoc]
  have hloc := fun v => loc D hU hc hr hW hR hk hrel2 v N
  choose τ δ U htr hdt hτ1 hδ1 hδr hU1 hδU hpow using hloc
  have hs0 : ∀ v, (D.ea v (z : Af F))⁻¹ ≠ 0 := fun v => inv_ne_zero ((z.isUnit.map (D.ea v)).ne_zero)
  have hσ : ∀ v (y : F), (((mkDat c χ).σ v y : ℝ) : ℂ) = v.embedding y := fun v y =>
    InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) y
  have hre : ∀ v (y : F), reAt v y = (mkDat c χ).σ v y := fun v y => by rw [reAt, ← hσ, Complex.ofReal_re]
  have hdpos : ∀ v, 0 < (mkDat c χ).σ v γ.val.det := fun v => by
    have := hell v
    nlinarith [sq_nonneg ((mkDat c χ).σ v γ.val.trace)]
  have hδ0 : ∀ v, δ v ≠ 0 := fun v h => by
    have h1 := hdt v
    rw [h, mul_zero, ← hσ] at h1
    exact (hdpos v).ne' (by exact_mod_cast h1)
  set A : ℝ := absF z with hA_def
  have hA : 0 < A := (Hm.absf F).1 z
  set Nw : ℝ := (W.map fun w => (normV w : ℝ)).prod with hNw
  have hp : ∏ v, (mkDat c χ).σ v γ.val.det = A ^ 2 * Nw := by
    rw [hA_def, hNw, ← prod_reAt hR hk hrel1]
    exact Finset.prod_congr rfl fun v _ => by rw [hre, abs_of_pos (hdpos v)]
  have hN : 0 < Nw := by
    have h1 : 0 < A ^ 2 * Nw := hp ▸ Finset.prod_pos fun v _ => hdpos v
    exact pos_of_mul_pos_right h1 (by positivity)
  have hreal : (W.map fun w => (normV w : ℝ) ^ ((k₀ : ℝ) / 2 - 1)).prod * ∏ v, (mkDat c χ).σ v γ.val.det ^ (1 - (k₀ : ℝ) / 2) =
      (A ^ (k₀ - 2))⁻¹ := by
    rw [Real.list_prod_map_rpow' W (fun w => (normV w : ℝ)) (fun _ _ => Nat.cast_nonneg _),
      Real.finsetProd_rpow _ _ (fun v _ => (hdpos v).le), hp, ← hNw]
    have e1 : (A ^ 2 * Nw) ^ (1 - (k₀ : ℝ) / 2) = (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) * Nw ^ (1 - (k₀ : ℝ) / 2) :=
      Real.mul_rpow (by positivity) hN.le
    have e2 : Nw ^ ((k₀ : ℝ) / 2 - 1) * Nw ^ (1 - (k₀ : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hN, show (k₀ : ℝ) / 2 - 1 + (1 - (k₀ : ℝ) / 2) = 0 by ring, Real.rpow_zero]
    have e3 : (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) = (A ^ (k₀ - 2))⁻¹ := by
      rw [← Real.rpow_natCast_mul hA.le, show ((2 : ℕ) : ℝ) * (1 - (k₀ : ℝ) / 2) = -((k₀ - 2 : ℕ) : ℝ) by
        rw [Nat.cast_sub hk₀]; push_cast; ring, Real.rpow_neg hA.le, Real.rpow_natCast]
    rw [e1, ← e3]
    calc Nw ^ ((k₀ : ℝ) / 2 - 1) * ((A ^ 2) ^ (1 - (k₀ : ℝ) / 2) * Nw ^ (1 - (k₀ : ℝ) / 2))
        = (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) * (Nw ^ ((k₀ : ℝ) / 2 - 1) * Nw ^ (1 - (k₀ : ℝ) / 2)) := by ring
      _ = (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) := by rw [e2, mul_one]
  set Q : ℂ := (((A : ℂ) * ∏ v, D.ea v (z : Af F)) ^ (k₀ - 2))⁻¹ with hQ
  have key : ∀ t' : InfinitePlace F → ℕ, (W.map (nz D k₀ t')).prod * (mkDat c χ).orb (fun v => k₀ + 2 * t' v) γ =
      Q * ∏ v, -(ch (τ v) (δ v) (k₀ + 2 * t' v - 1) * U v ^ t' v) := by
    intro t'
    rw [nz_prod]
    simp only [Dat.orb]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl fun v _ => term_v k₀ (t' v) (W.count (D.pl v)) hk₀ _ (τ v) (δ v) (U v) (l : ℂ) (hs0 v) (hδ0 v)
      (hδU v) _ _ (hdpos v) (by rw [hσ]; exact htr v) (by rw [hσ]; exact hdt v)]
    rw [Finset.prod_mul_distrib, ← mul_assoc]
    congr 1
    rw [Finset.prod_mul_distrib, list_prod_ofReal, mul_comm (∏ v, _ ^ (k₀ - 2)), ← mul_assoc, ← Complex.ofReal_prod,
      ← Complex.ofReal_mul, hreal, hQ, mul_pow, mul_inv, Finset.prod_pow, Finset.prod_inv_distrib, Complex.ofReal_inv,
      Complex.ofReal_pow, inv_pow]
  have hQ1 : nu ι Q = 1 := by
    rw [hQ, map_inv₀, map_pow, hA_def, (hMod F l ι D z).2, one_pow, inv_one]
  have hcong := fun v => local_cong (nu ι) hG (τ v) (δ v) (U v) (max (nu ι l ^ N) (nu ι l ^ r)) k₀ (t v) hk₀ (hτ1 v) (hδ1 v)
    ((hδr v).trans (le_max_right _ _)) ((hpow v (t v) (ht v)).1.trans (le_max_left _ _)) (hU1 v)
    ((hpow v (t v) (ht v)).2.trans (le_max_left _ _))
  obtain ⟨p1, p2, p3⟩ := val_prod_sub (nu ι) Finset.univ (fun v => -(ch (τ v) (δ v) (k₀ - 1)))
    (fun v => -(ch (τ v) (δ v) (k₀ + 2 * t v - 1) * U v ^ t v)) (max (nu ι l ^ N) (nu ι l ^ r))
    (fun v _ => by rw [Valuation.map_neg]; exact (hcong v).1) (fun v _ => by rw [Valuation.map_neg]; exact (hcong v).2.1)
    (fun v _ => by rw [neg_sub_neg, Valuation.map_sub_swap]; exact (hcong v).2.2)
  have h0 := key 0
  simp only [Pi.zero_apply, mul_zero, add_zero, pow_zero, mul_one] at h0
  rw [h0, key t]
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, hQ1, one_mul]; exact p1
  · rw [map_mul, hQ1, one_mul]; exact p2
  · rw [← mul_sub, map_mul, hQ1, one_mul]; exact p3
end
end
end

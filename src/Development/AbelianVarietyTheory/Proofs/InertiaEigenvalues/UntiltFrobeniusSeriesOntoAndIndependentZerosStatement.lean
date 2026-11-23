module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallBoundsUltrametricStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparatedRootsAdditivePoly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesEqPolynomialModPrimeStatement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentModPrimeOfPowLeCard

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem exists_linearIndependent_of_pow_le_card_zmod (l : ℕ) [Fact l.Prime] {Q ι : Type} [AddCommGroup Q] [Module (ZMod l) Q]
    (Z : Finset ι) (w : ι → Q) (hinj : Set.InjOn w Z) (h : ℕ) (hcard : l ^ h ≤ Z.card) :
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ LinearIndependent (ZMod l) (fun a => w (x a)) := by
  classical
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hs : (Z.image w).card = Z.card := Finset.card_image_of_injOn hinj
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent (ZMod l) ((Z.image w : Finset Q) : Set Q)
  have hbfin : b.Finite := (Finset.finite_toSet _).subset hbs
  haveI : Fintype b := hbfin.fintype
  have hrange : ∀ y ∈ Z.image w, ∃ f : b → ZMod l, ∑ c, f c • (c : Q) = y := by
    intro y hy
    have hy' : y ∈ Submodule.span (ZMod l) b := by
      rw [hspan]; exact Submodule.subset_span (by exact_mod_cast hy)
    rw [← Subtype.range_coe (s := b)] at hy'
    exact (Submodule.mem_span_range_iff_exists_fun (ZMod l)).1 hy'
  have hle : (Z.image w).card ≤ l ^ Fintype.card b := by
    have h3 : (Z.image w).card ≤ (Finset.univ.image (fun f : b → ZMod l => ∑ c, f c • (c : Q))).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨f, hf⟩ := hrange y hy
      exact Finset.mem_image.2 ⟨f, Finset.mem_univ _, hf⟩
    calc _ ≤ _ := h3
      _ ≤ (Finset.univ : Finset (b → ZMod l)).card := Finset.card_image_le
      _ = l ^ Fintype.card b := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card]
  have hhb : h ≤ Fintype.card b := by
    have : l ^ h ≤ l ^ Fintype.card b := hcard.trans (hs ▸ hle)
    exact (Nat.pow_le_pow_iff_right hl1).1 this
  let e : Fin h ↪ b := (Fin.castLEEmb hhb).trans (Fintype.equivFin b).symm.toEmbedding
  have hpre : ∀ c : b, ∃ i ∈ Z, w i = c := fun c => Finset.mem_image.1 (hbs c.2)
  choose g hgZ hgw using hpre
  refine ⟨fun a => g (e a), fun a => hgZ _, ?_⟩
  have hli' : LinearIndependent (ZMod l) (fun a => ((e a : b) : Q)) := hli.comp e e.injective
  convert hli' using 1
  funext a
  exact hgw (e a)

theorem ph_a_basis : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ)
    (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card →
    (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') →
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by
  intro l _ V ι _ K' h Z v hl hcard hdist
  have hQ : ∀ y : V ⧸ K', l • y = 0 := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z => rw [← QuotientAddGroup.mk_nsmul, hl z]; rfl
  letI : Module (ZMod l) (V ⧸ K') := AddCommGroup.zmodModule hQ
  have hinj : Set.InjOn (fun i => (v i : V ⧸ K')) Z := by
    intro i hi i' hi' he
    by_contra hne
    exact hdist i hi i' hi' hne ((QuotientAddGroup.eq_iff_sub_mem).1 he)
  obtain ⟨x, hxZ, hli⟩ := exists_linearIndependent_of_pow_le_card_zmod l Z (fun i => (v i : V ⧸ K')) hinj h hcard
  refine ⟨x, hxZ, ?_⟩
  intro n hn a
  have hm : QuotientAddGroup.mk' K' (∑ a, n a • v (x a)) = 0 := (QuotientAddGroup.eq_zero_iff _).2 hn

  rw [map_sum] at hm
  simp only [map_nsmul, QuotientAddGroup.mk'_apply] at hm
  have hsum : ∑ a, (n a : ZMod l) • ((v (x a) : V ⧸ K')) = 0 := by
    rw [← hm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
  have hz := Fintype.linearIndependent_iff.1 hli (fun a => (n a : ZMod l)) hsum a
  exact (ZMod.natCast_eq_zero_iff _ _).1 hz

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentModPrimeOfPowLeCardStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_independent_mod_prime_of_pow_le_card : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ) (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card → (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') → ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by
  first | exact @GlobalTheory.ph_a_basis | exact GlobalTheory.ph_a_basis | (intros; apply GlobalTheory.ph_a_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OntoOCAdditivePoly

section

@[expose] public section

open Polynomial

theorem GlobalTheory.onto_OC_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by
  intro l hl E N a hNE ha haN b hb
  set f : ℂ_[l][X] := (∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k)) - C b with hf
  have hl1 : 1 < l := hl.out.one_lt
  have hinj : Function.Injective (fun k : ℕ => l ^ k) := Nat.pow_right_injective hl.out.two_le
  have hcoeff : ∀ j, f.coeff j = (∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0) - (if j = 0 then b else 0) := by
    intro j
    simp only [hf, coeff_sub, finsetSum_coeff, coeff_monomial, coeff_C, Finsupp.single_apply]
  have hcN : f.coeff (l ^ N) = a N := by
    rw [hcoeff]
    have h0 : l ^ N ≠ 0 := pow_ne_zero _ (by omega)
    rw [if_neg h0, sub_zero, Finset.sum_eq_single N]
    · simp
    · intro k _ hk; rw [if_neg]; intro h; exact hk (hinj h)
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hbound : ∀ j, ‖f.coeff j‖ ≤ 1 := by
    intro j
    rw [hcoeff]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro k hk
      split_ifs
      · exact ha k (by have := Finset.mem_range.1 hk; omega)
      · simp
    · rw [norm_neg]; split_ifs
      · exact hb
      · simp
  have hne : f.coeff (l ^ N) ≠ 0 := by
    rw [hcN]; intro h; rw [h, norm_zero] at haN; exact zero_ne_one haN
  have key := (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] f 1 (l ^ N) zero_lt_one hne).1 (by
    intro j; simp only [one_pow, mul_one]; rw [hcN, haN]; exact hbound j)
  have hpos : 0 < Multiset.card (f.roots.filter fun z => ‖z‖ ≤ 1) :=
    lt_of_lt_of_le (pow_pos (by omega) N) key
  obtain ⟨W, hW⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  rw [Multiset.mem_filter] at hW
  obtain ⟨hr, hWn⟩ := hW
  refine ⟨W, hWn, ?_⟩
  have hroot := (mem_roots'.1 hr).2
  rw [IsRoot, hf, eval_sub, eval_finsetSum, eval_C] at hroot
  simp only [eval_monomial] at hroot
  exact sub_eq_zero.1 hroot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OntoOCAdditivePolyStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by
  first | exact @GlobalTheory.onto_OC_additive_poly | exact GlobalTheory.onto_OC_additive_poly | (intros; apply GlobalTheory.onto_OC_additive_poly <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparatedRootsAdditivePolyStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_separated_roots_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E M h : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), M + h ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a (M + h)‖ = 1 → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ∃ Z : Finset ℂ_[l], l ^ h ≤ Z.card ∧ (∀ W ∈ Z, ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = 0) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  first | exact @GlobalTheory.separated_roots_additive_poly | exact GlobalTheory.separated_roots_additive_poly | (intros; apply GlobalTheory.separated_roots_additive_poly <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesOntoAndIndependentZeros

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem GlobalTheory.oneVarCount_onto_independentZeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 → ∃ τ : ℝ, (∀ t : ℂ_[l], ‖t‖ ≤ τ → ∃ y : Fl l, ‖sh y‖ ≤ ‖(l : ℂ_[l])‖ ∧ ‖∑ i : Fin h, μ i * lam h i y - t‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∃ x : Fin h → Fl l, (∀ a, ‖sh (x a)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ‖∑ i : Fin h, μ i * lam h i (x a)‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∀ n : Fin h → ℕ, ‖sh (∑ a, n a • x a)‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h → ∀ a, l ∣ n a := by
  intro l _ h μ hh hμ
  obtain ⟨sh1, sh0, shmul, shpow, shle, shsurj, shadd, shneg⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hlD : ∀ D : ℕ, l ^ D ≠ 0 := fun D => (pow_pos (Fact.out : l.Prime).pos D).ne'
  obtain ⟨σ, hσ⟩ := shsurj (l : ℂ_[l]) hl1.le
  obtain ⟨t, D, E, M, a, ρ, ht, hME, ha, haN, hρl, hρ1, hρD, haM, hak, hpoly⟩ :=
    GlobalTheory.T.untiltFrobeniusLaurentSeries_eq_polynomial_mod_prime l h μ σ hh hμ hσ
  have hshv : ∀ u : Fl l, ‖sh (σ * u ^ l ^ D)‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro u
    rw [shmul, shpow, hσ, norm_mul, norm_pow]
    calc ‖(l : ℂ_[l])‖ * ‖sh u‖ ^ l ^ D ≤ ‖(l : ℂ_[l])‖ * 1 := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) (shle u)
      _ = _ := mul_one _
  refine ⟨‖t‖, ?_, ?_⟩
  · intro t' ht'
    have hb : ‖t' / t‖ ≤ 1 := by
      rw [norm_div]; exact div_le_one_of_le₀ ht' (norm_nonneg _)
    obtain ⟨W, hW, hPW⟩ := GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff l E (M + h) a hME ha haN (t' / t) hb
    obtain ⟨u, hu⟩ := shsurj W hW
    refine ⟨σ * u ^ l ^ D, hshv u, ?_⟩
    have key := hpoly u
    have e : t * (t' / t) = t' := by field_simp
    rw [hu, hPW, e] at key
    exact key
  · have hρ0 : 0 < ρ := lt_of_lt_of_le hl0 hρl
    obtain ⟨Z, hZc, hZ, hsep⟩ := GlobalTheory.T.exists_separated_roots_additive_poly l E M h a ρ hME ha haN hρ0 hρ1 haM hak
    choose! u hu using fun (W : ℂ_[l]) (hW : ‖W‖ ≤ 1) => shsurj W hW
    let v : ℂ_[l] → Fl l := fun W => σ * u W ^ l ^ D
    let K' : AddSubgroup (Fl l) :=
      { carrier := {x | ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h}
        zero_mem' := by
          show ‖sh (0 : Fl l)‖ ≤ _
          rw [sh0, norm_zero]; positivity
        add_mem' := by
          intro x y hx hy
          exact (GlobalTheory.T.tiltUntilt_add_estimate_le l _ x y hx hy).2
        neg_mem' := by
          intro x hx
          show ‖sh (-x)‖ ≤ _
          rw [shneg]; exact hx }
    have hchar : ∀ x : Fl l, l • x = 0 := fun x => by
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have hsepv : ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → v W - v W' ∉ K' := by
      intro W hW W' hW' hne hmem
      have hsepW := hsep W hW W' hW' hne
      have hvd : v W - v W' = σ * (u W - u W') ^ l ^ D := by
        simp only [v]; rw [sub_pow_char_pow, mul_sub]
      have hmem' : ‖sh (v W - v W')‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h := hmem
      rw [hvd, shmul, shpow, hσ, norm_mul, norm_pow, ← hρD] at hmem'
      have hd : ‖sh (u W - u W')‖ ≤ ρ := by
        by_contra hcon
        push_neg at hcon
        have h1 : ρ ^ l ^ D < ‖sh (u W - u W')‖ ^ l ^ D := pow_lt_pow_left₀ hcon hρ0.le (hlD D)
        have h2 := mul_lt_mul_of_pos_left h1 hl0
        linarith
      have h2 := shadd (u W - u W') (u W')
      rw [sub_add_cancel, hu W (hZ W hW).1, hu W' (hZ W' hW').1] at h2
      have e3 : W - W' = (W - sh (u W - u W') - W') + sh (u W - u W') := by ring
      have h3 : ‖W - W'‖ ≤ max ‖W - sh (u W - u W') - W'‖ ‖sh (u W - u W')‖ := by
        rw [e3]; exact IsUltrametricDist.norm_add_le_max _ _
      have h4 : ‖W - W'‖ ≤ ρ := h3.trans (max_le (h2.trans hρl) hd)
      linarith
    obtain ⟨x, hxZ, hx⟩ := GlobalTheory.T.exists_independent_mod_prime_of_pow_le_card l (Fl l) ℂ_[l] K' h Z v hchar hZc hsepv
    refine ⟨fun b => v (x b), fun b => hshv (u (x b)), ?_, fun n hn => hx n hn⟩
    intro b
    have key := hpoly (u (x b))
    rw [hu _ (hZ _ (hxZ b)).1, (hZ _ (hxZ b)).2, mul_zero, sub_zero] at key
    exact key
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesOntoAndIndependentZerosStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusSeries_onto_and_independent_zeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 → ∃ τ : ℝ, (∀ t : ℂ_[l], ‖t‖ ≤ τ → ∃ y : Fl l, ‖sh y‖ ≤ ‖(l : ℂ_[l])‖ ∧ ‖∑ i : Fin h, μ i * lam h i y - t‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∃ x : Fin h → Fl l, (∀ a, ‖sh (x a)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ‖∑ i : Fin h, μ i * lam h i (x a)‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∀ n : Fin h → ℕ, ‖sh (∑ a, n a • x a)‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h → ∀ a, l ∣ n a := by
  first | exact @GlobalTheory.oneVarCount_onto_independentZeros | exact GlobalTheory.oneVarCount_onto_independentZeros | (intros; apply GlobalTheory.oneVarCount_onto_independentZeros <;> assumption)
end
end

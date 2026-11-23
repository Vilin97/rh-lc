module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.PlaneGramTheoremOfLemmas
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SecondValuationOfAdmitted
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrBase
public import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Linter.Style
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
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.UnitLevelOne
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrSpanG
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
import Mathlib.Data.Finset.Slice
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrRenExpandMonomial

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData

section Mono

variable {K : Type} [Field K] {r : ℕ}

theorem br_monomial_eq (s : Fin r →₀ ℕ) (c : K) :
    (monomial s c : MvPolynomial (Fin r) K) = C c * ∏ a, X a ^ s a := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun a => pow_zero _)]

def brRen (K : Type) [Field K] (r : ℕ) : MvPolynomial (Fin r) K →ₐ[K] MvPolynomial (Unit × Fin r) K :=
  rename fun a => ((), a)

theorem brRen_inj : Function.Injective (fun a : Fin r => ((), a)) := fun a b h => congrArg Prod.snd h

theorem brRen_monomial (s : Fin r →₀ ℕ) (c : K) : brRen K r (monomial s c) = C c * monoL (K := K) (fun a => s a) := by
  rw [br_monomial_eq, map_mul, map_prod]
  simp only [brRen, rename_C, map_pow, rename_X, monoL]

theorem brRen_expand_monomial (P : ℕ) (s : Fin r →₀ ℕ) (c : K) :
    brRen K r (expand P (monomial s c)) = C c * monoL (K := K) (fun a => P * s a) := by
  rw [br_monomial_eq]
  simp only [map_mul, map_prod, map_pow, expand_C, expand_X, brRen, rename_C, rename_X, monoL, ← pow_mul]

theorem br_ddiv_monomial (M α : Fin r →₀ ℕ) :
    ddiv M (monomial α (1 : K)) = monomial (α - M) (∏ a, (((α a).choose (M a) : ℕ) : K)) := by
  classical
  unfold ddiv
  rw [support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_mul]
  split_ifs with h
  · congr 1
    rw [Finsupp.prod]
    push_cast
    apply Finset.prod_subset (Finset.subset_univ _)
    intro a _ ha
    have h0 : α a = 0 := by simpa using ha
    have hM : M a = 0 := by
      have := Finsupp.le_def.1 h a
      omega
    simp [h0, hM]
  · obtain ⟨a, ha⟩ : ∃ a, α a < M a := by
      by_contra hc
      push_neg at hc
      exact h (Finsupp.le_def.2 hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Nat.choose_eq_zero_of_lt ha]), monomial_zero]

theorem brRen_ddiv (M α : Fin r →₀ ℕ) :
    brRen K r (ddiv M (monomial α (1 : K))) =
      divDer (atLetter () (fun a => M a)) (monoL (K := K) (fun a => α a)) := by
  rw [br_ddiv_monomial, brRen_monomial, Formalism.MainNotions.G.Joints.divDer_monoL]
  congr 2

theorem brRen_term (P : ℕ) (ρ' δ κ β : Fin r →₀ ℕ) (x : K) :
    brRen K r (monomial ρ' x * expand P (monomial δ (1 : K) * ddiv κ (monomial β (1 : K)))) =
      C (x * ∏ a, (((β a).choose (κ a) : ℕ) : K)) * monoL (K := K) (fun a => ρ' a) *
        monoL (K := K) (fun a => P * (β a - κ a + δ a)) := by
  rw [br_ddiv_monomial, monomial_mul, one_mul, map_mul, brRen_monomial, brRen_expand_monomial]
  have h : (fun a => P * (δ + (β - κ)) a) = fun a => P * (β a - κ a + δ a) := by
    funext a
    simp [Finsupp.add_apply, add_comm]
  rw [h, map_mul]
  ring

end Mono

section DER

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem brDER (S0 : UniformizedDVR p O) [CharZero (KK O)] (h6 : Formalism.MainNotions.PlaneGramData.DerivativeCongruenceAtRing p O) :
    DER (KK O) (vQ p S0) p := by
  classical
  unfold DER
  intro _ r g ρ hρ M c hc
  obtain ⟨T, coef, hT, hval⟩ := h6 g r (fun a => M a) (fun a => ρ a) hρ c hc
  let e := T.equivFin
  let τ : Fin T.card → (Fin r → ℕ) × (Fin r → ℕ) × (Fin r → ℕ) := fun t => (e.symm t).1
  have key : ∀ x : WithTop ℚ, geQ x (c : ℝ) → ((c : ℕ) : WithTop ℚ) ≤ x := by
    intro x hx
    induction x using WithTop.recTopCoe with
    | top => exact le_top
    | coe q =>
      have hq := hx q rfl
      have hq' : ((c : ℕ) : ℚ) ≤ q := by exact_mod_cast hq
      exact_mod_cast hq'
  refine ⟨T.card, fun t => algebraMap O (KK O) (coef (τ t)),
    fun t => Finsupp.equivFunOnFinite.symm (τ t).1, fun t => Finsupp.equivFunOnFinite.symm (τ t).2.1,
    fun t => Finsupp.equivFunOnFinite.symm (τ t).2.2, ?_, ?_, ?_⟩
  · intro t
    show (0 : WithTop ℚ) ≤ vK p (algebraMap O (KK O) (coef (τ t)))
    by_cases h0 : coef (τ t) = 0
    · rw [h0, map_zero, Formalism.MainNotions.G.GLWeightTheory.valuation_zero_alt p]
      exact le_top
    · rw [Formalism.MainNotions.G.Joints.vK_alg p _ h0]
      exact WithTop.coe_nonneg.2 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · intro t
    have hb := (hT (τ t) (e.symm t).2).2
    rw [br_absE, br_absE]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    push_cast at hb ⊢
    exact hb
  · intro β γ
    show ((c : ℕ) : WithTop ℚ) ≤ vK p _
    have hX : ∀ F : MvPolynomial (Fin r) (KK O),
        F.coeff γ = (brRen (KK O) r F).coeff (γ.mapDomain fun a => ((), a)) :=
      fun F => (coeff_rename_mapDomain _ brRen_inj F γ).symm

    rw [hX, map_sub, map_sum, brRen_ddiv]
    simp only [brRen_term]
    have hα : (fun a => (ρ + p ^ g • β) a) = fun a => ρ a + p ^ g * β a := by
      funext a
      simp
    have hsum : (∑ t : Fin T.card,
        C (algebraMap O (KK O) (coef (τ t)) *
            ∏ a, (((β a).choose ((Finsupp.equivFunOnFinite.symm (τ t).2.2) a) : ℕ) : KK O)) *
          monoL (K := KK O) (fun a => (Finsupp.equivFunOnFinite.symm (τ t).1) a) *
          monoL (K := KK O) (fun a => p ^ g * (β a - (Finsupp.equivFunOnFinite.symm (τ t).2.2) a +
            (Finsupp.equivFunOnFinite.symm (τ t).2.1) a))) =
        ∑ x ∈ T, C (algebraMap O (KK O) (coef x) * ∏ a, (((β a).choose (x.2.2 a) : ℕ) : KK O)) *
          monoL (K := KK O) x.1 * monoL (K := KK O) (fun a => p ^ g * (β a - x.2.2 a + x.2.1 a)) := by
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      rw [← Finset.sum_coe_sort T]
      exact Fintype.sum_equiv e.symm _ _ (fun t => rfl)
    rw [hα, hsum]
    exact key _ (hval (fun a => β a) (γ.mapDomain fun a => ((), a)))

end DER

end Formalism.MainNotions.PlaneGram
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrSpan

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G.Joints.PlaneGramSpan

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem coe_initSet_zero (N : ℕ) : ((initSet N 0 : Finset (Fin N)) : Set (Fin N)) = ∅ := by
  ext j; simp [initSet]

theorem coe_initSet_succ (N : ℕ) (i : Fin N) :
    ((initSet N (i.succ : Fin (N + 1)).val : Finset (Fin N)) : Set (Fin N)) = {j | j ≤ i} := by
  ext j
  simp only [initSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Fin.val_succ]
  rw [Fin.le_iff_val_le_val]
  omega

theorem brSPAN [CharZero (G.KK O)] (S : G.UniformizedDVR p O) (h3 : Formalism.MainNotions.PlaneGramData.PolynomialSpanAtRing O) :
    SPAN (G.KK O) (vQ p S) p := by
  classical
  intro _ N r _ sg d
  obtain ⟨h3a, h3b, h3c⟩ := h3
  let LL : G.Letters (Fin N) := ⟨sg⟩
  haveI : Finite (Idx N r LL d) := idx_finite h3a N r LL d
  letI : Fintype (Idx N r LL d) := Fintype.ofFinite _
  have hint : ∀ F : MvPolynomial (Fin N × Fin r) (G.KK O), Integral (vQ p S) F →
      ∀ m, ∃ o : O, AddMonoidAlgebra.coeff F m = algebraMap O (G.KK O) o :=
    fun F hF m => (vQ_nonneg_iff S _).1 (hF m)
  let cI : (b : Idx N r LL d) → Fin #(G.colRange b.1.1.mu) → ℤ :=
    fun b k => ((G.colRange b.1.1.mu).equivFin.symm k : ℤ)
  refine ⟨Idx N r LL d, inferInstance, fun b => G.Psi (G.KK O) b.1.1.mu b.1.2, fun b => b.1.1.mu,
    fun b => #(G.colRange b.1.1.mu), fun b k => G.Kcol (G.KK O) b.1.1.mu (cI b k) N (b.1.2 (cI b k)),
    cI, fun b k i => b.1.1.h i (cI b k),
    fun b k => Finset.univ.filter (fun i => G.IsUsed b.1.1.mu (cI b k) i),
    ?_, li_K h3a N r LL d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    refine ⟨?_, ?_⟩
    · rw [PolK_eq]
      exact (psiK_mem h3a b).1
    · intro m
      obtain ⟨o, ho⟩ := (psiK_mem h3a b).2 m
      rw [ho]
      exact (vQ_nonneg_iff S _).2 ⟨o, rfl⟩
  · intro F hF
    obtain ⟨hFK, hFI⟩ := hF
    rw [PolK_eq] at hFK
    obtain ⟨l, hl⟩ := span_all (LL := LL) h3a F hFK (hint F hFI)
    exact ⟨fun b => algebraMap O _ (l b), fun b => (vQ_nonneg_iff S _).2 ⟨_, rfl⟩, hl⟩
  · rintro th F ⟨⟨hFK, hFI⟩, hA⟩
    rw [PolK_eq] at hFK
    have hth : ∀ i : Fin N, ((th i.succ : ℤ) : WithTop ℤ) ≤ G.valS LL {j | j ≤ i} F := by
      intro i
      have h1 := hA i.succ
      change ((th i.succ : ℤ) : WithTop ℤ) ≤ valS sg (initSet N (i.succ : Fin (N + 1)).val) F at h1
      rw [valS_eq, coe_initSet_succ] at h1
      exact h1
    obtain ⟨l, hl1, hl2⟩ := span_mem h3b F hFK (hint F hFI) (fun i => th i.succ) hth
    refine ⟨fun b => algebraMap O _ (l b), fun b => (vQ_nonneg_iff S _).2 ⟨_, rfl⟩, ?_, hl2⟩
    intro b hb i
    have hlb : l b ≠ 0 := by
      intro h0
      apply hb
      simp [h0]
    dsimp only
    rw [lastIdx_eq]
    cases i using Fin.cases with
    | zero =>
      rw [b.1.1.zero]
      have hF0 : F ≠ 0 := by
        intro hF0
        rw [hF0] at hl2
        have hz := Fintype.linearIndependent_iff.1 (li_K h3a N r LL d) _ hl2.symm b
        exact hlb (IsFractionRing.injective O (G.KK O) (by rw [hz, map_zero]))
      have h0 := hA 0
      change ((th 0 : ℤ) : WithTop ℤ) ≤ valS sg (initSet N (0 : Fin (N + 1)).val) F at h0
      rw [valS_eq, Fin.val_zero, coe_initSet_zero] at h0
      exact valS_empty_le LL F hF0 _ h0
    | succ j => exact hl1 b hlb j
  · intro b
    exact (prod_fin_equiv (G.colRange b.1.1.mu) (fun c => G.Kcol (G.KK O) b.1.1.mu c N (b.1.2 c))).symm
  · intro b k
    dsimp only
    rw [PolK, mem_restrictSupport_iff]
    intro m hm
    rw [← Formalism.MainNotions.G.Joints.StandardMonomialSpace.lift_Kcol_map (algebraMap O (G.KK O))] at hm
    have hm' := MvPolynomial.support_map_subset _ _ hm
    intro i
    have h1 := (h3c N r LL d b.1.1).1 (cI b k) (b.1.2 (cI b k)) i m hm'
    simpa [G.multideg] using h1
  · intro b i
    rw [← (h3c N r LL d b.1.1).2.1 i]
    refine Finset.card_bij (fun k _ => (((G.colRange b.1.1.mu).equivFin.symm k : ℤ))) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨Subtype.prop _, hk⟩
    · intro k1 _ k2 _ h
      exact (G.colRange b.1.1.mu).equivFin.symm.injective (Subtype.ext h)
    · intro c hc
      simp only [Finset.mem_filter] at hc
      refine ⟨(G.colRange b.1.1.mu).equivFin ⟨c, hc.1⟩, ?_, ?_⟩
      · simp [cI, hc.2]
      · simp
  · intro b k i hc
    refine ((h3c N r LL d b.1.1).2.2.2.1 (cI b k) hc i).trans (le_of_eq ?_)
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LL]
    tauto
  · intro b k i
    dsimp only
    rw [valS_eq]
    cases i using Fin.cases with
    | zero =>
      rw [Fin.val_zero, coe_initSet_zero]
      have hv0 : colVal (cI b k) (b.1.1.h 0 (cI b k)) r = 0 := by
        show colVal (cI b k) (G.colH (b.1.1.mu 0) (cI b k)) r = 0
        rw [b.1.1.zero, colH_zero]
        have hr := NeZero.ne r
        simp only [colVal]
        split_ifs <;> omega
      rw [hv0]
      exact valS_empty_nonneg LL _
    | succ j =>
      rw [coe_initSet_succ]
      exact col_est h3b b.1.1 (cI b k) (b.1.2 (cI b k)) (b.2.2.1 (cI b k)) j
  · intro b i
    dsimp only
    rw [lastIdx_eq, stage_identity b.1.1 i]
    exact (sum_fin_equiv _ (fun c => colVal c (b.1.1.h i c) r)).symm

end Formalism.MainNotions.PlaneGram
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G

theorem stmt (D : Formalism.BasicNotions.D7) {CH : ℝ} (hCH : 26 ≤ CH) : Formalism.MainNotions.PlaneGramData.Stmt D CH 2 24 60 := by
  intro p O _ _ _ _ hSet hAdm
  obtain ⟨⟨S⟩, n', hG⟩ := hSet
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hAdm
  exact Br.plane_gram_of_theorem_at S hG
    (plane_gram_theorem_of_five_lemmas le_rfl (second_valuation_of_admitted h2) (brSPAN S h3) (brPROJ S h4) (brDIG D S hG h5)
      (brDER S h6)) hCH

theorem stmtE (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaneGramData.ClosedFormOfAdmitted D :=
  ⟨26, 2, 24, 60, by norm_num, by norm_num, by norm_num, by norm_num, fun _ hCH => stmt D hCH⟩

end Formalism.MainNotions.PlaneGram
end
end
end

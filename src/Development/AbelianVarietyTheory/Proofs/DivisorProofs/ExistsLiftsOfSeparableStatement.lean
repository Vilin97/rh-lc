module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LiftInvariantsFinrankEq
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.FieldTheory.IsAlgClosed.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Imports

section

@[expose] public section

namespace GlobalTheory.MaximalIdealMembership

theorem mem_maximalIdeal_iff {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (f : MvPowerSeries (Fin a) O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ↔
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

end GlobalTheory.MaximalIdealMembership
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemPowOfCoeffMem

section

@[expose] public section

namespace GlobalTheory.PowerSeriesIdealPowers

open MvPowerSeries IsLocalRing

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem mem_max_iff {σ : Type} (f : MvPowerSeries σ O) :
    f ∈ maximalIdeal (MvPowerSeries σ O) ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]

theorem mem_smul_top_iff {S : Type} [CommRing S] (I : Ideal S) (x : S) :
    x ∈ (I • ⊤ : Submodule S S) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem coeff_mem_of_mem_pow {σ : Type} (n : ℕ) :
    ∀ f ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n, ∀ d : σ →₀ ℕ,
      coeff d f ∈ (maximalIdeal O) ^ (n - d.degree) := by
  classical
  induction n with
  | zero => intro f _ d; simp
  | succ n ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro x hx y hy d
      rw [coeff_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 := ih x hx p.1
      have h2 : coeff p.2 y ∈ (maximalIdeal O) ^ (1 - p.2.degree) := by
        by_cases h0 : p.2.degree = 0
        · rw [Finsupp.degree_eq_zero_iff] at h0
          rw [h0, coeff_zero_eq_constantCoeff_apply]
          simpa using (mem_max_iff y).1 hy
        · rw [show 1 - p.2.degree = 0 by omega]; simp
      have hdeg : d.degree = p.1.degree + p.2.degree := by rw [← hp, map_add (f := _)]
      have hle : n + 1 - d.degree ≤ (n - p.1.degree) + (1 - p.2.degree) := by omega
      exact Ideal.pow_le_pow_right hle (by rw [pow_add]; exact Ideal.mul_mem_mul h1 h2)
    · intro x y hx hy d
      rw [map_add (f := coeff d)]; exact add_mem (hx d) (hy d)

theorem coeff_X_mul_add {σ : Type} [DecidableEq σ] (i : σ) (g : MvPowerSeries σ O) (d : σ →₀ ℕ) :
    coeff (d + Finsupp.single i 1) (X i * g) = coeff d g := by
  rw [X, coeff_monomial_mul]
  simp

theorem C_mem_pow {σ : Type} (n : ℕ) (c : O) (hc : c ∈ (maximalIdeal O) ^ n) :
    C c ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n := by
  have h1 : C c ∈ Ideal.map (C (σ := σ)) ((maximalIdeal O) ^ n) := Ideal.mem_map_of_mem _ hc
  rw [Ideal.map_pow] at h1
  refine Ideal.pow_right_mono ?_ n h1
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_max_iff, constantCoeff_C]
  exact hx

theorem X_mem_max {σ : Type} (i : σ) : (X i : MvPowerSeries σ O) ∈ maximalIdeal (MvPowerSeries σ O) := by
  rw [mem_max_iff, constantCoeff_X]; exact zero_mem _

theorem mem_pow_of_coeff_mem (a n : ℕ) :
    ∀ f : MvPowerSeries (Fin a) O, (∀ d : Fin a →₀ ℕ, coeff d f ∈ (maximalIdeal O) ^ (n - d.degree)) →
      f ∈ (maximalIdeal (MvPowerSeries (Fin a) O)) ^ n := by
  classical
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    let P : Fin a → (Fin a →₀ ℕ) → Prop := fun i d => d i ≠ 0 ∧ ∀ j < i, d j = 0
    let fi : Fin a → MvPowerSeries (Fin a) O := fun i d => if P i d then coeff d f else 0
    have hfi : ∀ i d, coeff d (fi i) = if P i d then coeff d f else 0 := fun i d => rfl
    have huniq : ∀ i j d, P i d → P j d → i = j := by
      intro i j d hi hj
      rcases lt_trichotomy i j with h | h | h
      · exact absurd (hj.2 i h) hi.1
      · exact h
      · exact absurd (hi.2 j h) hj.1
    have hexists : ∀ d : Fin a →₀ ℕ, d ≠ 0 → ∃ i, P i d := by
      intro d hd
      have hs : d.support.Nonempty := Finsupp.support_nonempty_iff.2 hd
      refine ⟨d.support.min' hs, Finsupp.mem_support_iff.1 (Finset.min'_mem _ hs), fun j hj => ?_⟩
      by_contra hne
      exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.2 hne)) (not_le.2 hj)
    have hdecomp : f = C (constantCoeff f) + ∑ i, fi i := by
      ext d

      rw [map_add (f := _), map_sum, coeff_C]
      simp only [hfi]
      by_cases hd : d = 0
      · subst hd
        have : ∀ i, ¬ P i 0 := fun i h => h.1 rfl
        simp [this, coeff_zero_eq_constantCoeff_apply]
      · obtain ⟨i, hi⟩ := hexists d hd
        rw [if_neg hd, zero_add, Finset.sum_eq_single i (fun j _ hj => by
          rw [if_neg (fun h => hj (huniq _ _ _ h hi))]) (fun h => absurd (Finset.mem_univ i) h),
          if_pos hi]
    rw [hdecomp]
    refine add_mem (C_mem_pow _ _ ?_) (Ideal.sum_mem _ fun i _ => ?_)
    · simpa [coeff_zero_eq_constantCoeff_apply] using hf 0
    · have hdvd : (X i : MvPowerSeries (Fin a) O) ∣ fi i := by
        rw [X_dvd_iff]
        intro m hm
        rw [hfi, if_neg (fun h => h.1 hm)]
      obtain ⟨g, hg⟩ := hdvd
      rw [hg, pow_succ']
      refine Ideal.mul_mem_mul (X_mem_max i) (ih g fun d => ?_)
      rw [← coeff_X_mul_add i g d, ← hg, hfi]
      split_ifs
      · have := hf (d + Finsupp.single i 1)
        rwa [map_add, Finsupp.degree_single, show n + 1 - (d.degree + 1) = n - d.degree by omega] at this
      · exact zero_mem _

theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    [IsPrecomplete (IsLocalRing.maximalIdeal O) O] (a : ℕ),
    IsPrecomplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) := by
  intro O _ _ hO a
  constructor
  intro f hf
  simp only [SModEq.sub_mem, mem_smul_top_iff] at hf ⊢
  let s : (Fin a →₀ ℕ) → ℕ → O := fun d k => coeff d (f (k + d.degree))
  have hs : ∀ d, ∃ L : O, ∀ k, s d k ≡ L [SMOD ((maximalIdeal O) ^ k • ⊤ : Submodule O O)] := by
    intro d
    refine IsPrecomplete.prec hO ?_
    intro k l hkl
    rw [SModEq.sub_mem, mem_smul_top_iff]
    have h := coeff_mem_of_mem_pow (k + d.degree) _ (hf (Nat.add_le_add_right hkl _)) d
    rwa [map_sub, Nat.add_sub_cancel] at h
  choose L hL using hs
  let Lim : MvPowerSeries (Fin a) O := fun d => L d
  have hLim : ∀ d, coeff d Lim = L d := fun d => rfl
  refine ⟨Lim, fun n => mem_pow_of_coeff_mem a n _ fun d => ?_⟩
  rw [map_sub, hLim]
  by_cases hd : d.degree ≤ n
  · have h := hL d (n - d.degree)
    rw [SModEq.sub_mem, mem_smul_top_iff] at h
    simp only [s, Nat.sub_add_cancel hd] at h
    exact h
  · rw [show n - d.degree = 0 by omega]; simp
end GlobalTheory.PowerSeriesIdealPowers
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NoethLocalHausdorff

section

@[expose] public section

namespace GlobalTheory.NoetherianLocalHausdorff

theorem noeth_local_hausdorff : ∀ (B : Type) [inst : CommRing B] [inst_1 : IsLocalRing B] [IsNoetherianRing B],
    IsHausdorff (IsLocalRing.maximalIdeal B) B := by
  intro B _ _ _
  refine ⟨fun x hx => ?_⟩
  have h : x ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal B) ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    have := hx n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this
    exact this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal B).ne_top] at h
  exact (Submodule.mem_bot B).1 h

end GlobalTheory.NoetherianLocalHausdorff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoeffMemOfMemMaxPow

section

@[expose] public section

noncomputable section

open MvPowerSeries IsLocalRing Formalism.BasicNotions.V1

namespace GlobalTheory.PsCNL

section Division

variable {σ : Type} {O : Type} [CommRing O]

end Division

section

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem mem_max_iff (f : MvPowerSeries (Fin a) O) :
    f ∈ maximalIdeal (MvPowerSeries (Fin a) O) ↔ constantCoeff f ∈ maximalIdeal O :=
  _root_.GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff f

theorem ps_isPrecomplete [IsPrecomplete (maximalIdeal O) O] (a : ℕ) :
    IsPrecomplete (maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) :=
  _root_.GlobalTheory.PowerSeriesIdealPowers.main a

end

theorem haus_of_noeth (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    IsHausdorff (maximalIdeal B) B :=
  _root_.GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff B

theorem psCNL : ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : TR O) (n : ℕ),
    ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) C.C)), IsCNL O (MvPowerSeries (Fin n) C.C) ∧
      ∀ x : MvPowerSeries (Fin n) C.C, x ∈ maximalIdeal (MvPowerSeries (Fin n) C.C) ↔
        MvPowerSeries.constantCoeff x ∈ maximalIdeal C.C := by
  intro O _ _ A n
  refine ⟨inferInstance, ?_, fun x => mem_max_iff x⟩
  exact
    { noeth := inferInstance
      complete :=
        { toIsHausdorff := haus_of_noeth _
          toIsPrecomplete := ps_isPrecomplete n }
      localHom := ⟨fun a ha => by
        rw [MvPowerSeries.algebraMap_apply, isUnit_iff_constantCoeff, constantCoeff_C] at ha
        exact isUnit_of_map_unit _ _ ha⟩
      resSurj := by
        intro y
        obtain ⟨f, rfl⟩ := residue_surjective y
        obtain ⟨a, ha⟩ := IsCNL.resSurj (O := O) (A := A.C) (residue A.C (constantCoeff f))
        have ha' : residue A.C (algebraMap O A.C a) = residue A.C (constantCoeff f) := ha
        refine ⟨a, ?_⟩
        show residue _ (algebraMap O (MvPowerSeries (Fin n) A.C) a) = residue _ f
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
          isUnit_iff_constantCoeff, map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C]
        show algebraMap O A.C a - constantCoeff f ∈ maximalIdeal A.C
        rw [← residue_eq_zero_iff, map_sub, ha', sub_self] }

end GlobalTheory.PsCNL
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfSeparable

section

@[expose] public section

noncomputable section

open Filter Topology Polynomial IsLocalRing

namespace GlobalTheory.HenselSplitPS

instance isAdicComplete_maximalIdeal (D : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin D) ℂ)) (MvPowerSeries (Fin D) ℂ) := by
  have : IsPrecomplete (maximalIdeal ℂ) ℂ := by
    rw [IsLocalRing.maximalIdeal_eq_bot]; infer_instance
  exact { toIsHausdorff := GlobalTheory.PsCNL.haus_of_noeth _
          toIsPrecomplete := GlobalTheory.PsCNL.ps_isPrecomplete D }

theorem constantCoeff_eval (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)) (x : MvPowerSeries (Fin D) ℂ) :
    MvPowerSeries.constantCoeff (P.eval x) =
      (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).eval (MvPowerSeries.constantCoeff x) := by
  rw [eval_map, eval₂_hom]

theorem exists_lifts_of_separable : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic →
    (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable →
    ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) := by
  intro D P hP hsep
  set φ := MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ) with hφ
  set Q := P.map φ with hQ
  have hQdeg : Q.natDegree = P.natDegree := hP.natDegree_map φ
  have hcard : Q.roots.toFinset.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree, hQdeg]
  let e : Fin P.natDegree ≃ Q.roots.toFinset := (Q.roots.toFinset.equivFinOfCardEq hcard).symm
  have lift : ∀ c : ℂ, c ∈ Q.roots → ∃ a : MvPowerSeries (Fin D) ℂ, P.IsRoot a ∧ φ a = c := by
    intro c hc
    have hQ0 : Q ≠ 0 := (hP.map φ).ne_zero
    have hroot : Q.eval c = 0 := (mem_roots hQ0).1 hc
    have h1 : P.eval (MvPowerSeries.C c) ∈ maximalIdeal (MvPowerSeries (Fin D) ℂ) := by
      rw [GlobalTheory.PsCNL.mem_max_iff, constantCoeff_eval, MvPowerSeries.constantCoeff_C, ← hQ, hroot]
      exact zero_mem _
    have hder : Q.derivative.eval c ≠ 0 := by
      have := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := c) (by simpa [eval₂_id] using hroot)
      simpa [eval₂_id] using this
    have h2 : IsUnit (P.derivative.eval (MvPowerSeries.C c)) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_eval, MvPowerSeries.constantCoeff_C,
        ← derivative_map, ← hQ]
      exact hder.isUnit
    obtain ⟨a, ha, hac⟩ := HenselianRing.is_henselian (I := maximalIdeal (MvPowerSeries (Fin D) ℂ)) P hP
      (MvPowerSeries.C c) h1 (h2.map _)
    refine ⟨a, ha, ?_⟩
    rw [GlobalTheory.PsCNL.mem_max_iff, map_sub, MvPowerSeries.constantCoeff_C, IsLocalRing.maximalIdeal_eq_bot,
      Ideal.mem_bot, sub_eq_zero] at hac
    exact hac
  choose! θ hθ using lift
  refine ⟨fun j => θ (e j), fun i j hij => ?_, fun j => (hθ _ (Multiset.mem_toFinset.1 (e j).2)).1⟩
  have hi := (hθ _ (Multiset.mem_toFinset.1 (e i).2)).2
  have hj := (hθ _ (Multiset.mem_toFinset.1 (e j).2)).2
  have : ((e i : ℂ)) = e j := by rw [← hi, ← hj]; exact congrArg φ hij
  exact e.injective (Subtype.ext this)

end GlobalTheory.HenselSplitPS
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfSeparableStatement

section

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_lifts_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic → (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable → ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) := by
  first | exact @GlobalTheory.HenselSplitPS.exists_lifts_of_separable | exact GlobalTheory.HenselSplitPS.exists_lifts_of_separable | (intros; apply GlobalTheory.HenselSplitPS.exists_lifts_of_separable <;> assumption)
end
end

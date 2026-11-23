module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountGen
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.FFInert2Holds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFHS
public import Mathlib.FieldTheory.Galois.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ProdInertClosed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.SingleMulVec
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FfHSelfOfSnd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.SingleMulVec
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FixedMemRange

section

@[expose] public section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix Polynomial

theorem keyInert (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - 1 - (x - 1) * (x ^ (2 * n + 1) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - (-1) ^ n * x ^ (-(n : ℤ))) * (1 - (-1) ^ (n + 1) * x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, he.add_one.neg_one_pow]
    field_simp
    ring
  · rw [ho.neg_one_pow, ho.add_one.neg_one_pow]
    field_simp
    ring

theorem fixed_mem_range {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (h2 : Module.finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) (t : K) (ht : σ t = t) :
    ∃ c : k, t = algebraMap k K c := by
  classical
  haveI : FiniteDimensional k K := inferInstance
  haveI : IsGalois k K := inferInstance
  have hcard : Fintype.card (K ≃ₐ[k] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  have hall : ∀ τ : K ≃ₐ[k] K, τ = AlgEquiv.refl ∨ τ = σ := by
    intro τ
    by_contra h
    push_neg at h
    have h3 : ({AlgEquiv.refl, σ, τ} : Finset (K ≃ₐ[k] K)).card ≤ 2 := hcard ▸ Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hne, Ne.symm h.1]), Finset.card_pair (Ne.symm h.2)] at h3
    omega
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed t).mpr (fun τ => by
    rcases hall τ with rfl | rfl
    · rfl
    · exact ht)
  exact ⟨c, hc.symm⟩

end PI.OmVe
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertBHoldsAlt

section

@[expose] public section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW PI.VolStabSW.FFHS PI.OmLocU.CntFF Matrix

theorem fFInertB_holds : PI.OmVd.FFInertB := by
  intro k K _ _ _ _ σ hσ h2 hne M a haM J hJ hdJ T hT hTu
  classical
  obtain ⟨i₀, hr, hc, hu⟩ := hTu
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := i₀.pos; omega⟩
  have := Fintype.ofFinite k
  have : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  have : Finite K := Module.finite_of_finite k
  have := Fintype.ofFinite K
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have hJ' : ∀ i j, (σ : K →+* K) (J j i) = J i j := hJ
  have hu0 : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det := by
    have e := det_corOne T i₀ hr 1
    rw [one_mul] at e
    rw [← e]; exact hu
  have hTt : ∀ c : k, c ≠ 0 →
      (∀ i j, σ ((T + Matrix.single i₀ i₀ (algebraMap k K c)) j i) =
        (T + Matrix.single i₀ i₀ (algebraMap k K c)) i j) ∧
      IsUnit (T + Matrix.single i₀ i₀ (algebraMap k K c)).det := by
    intro c hc0
    refine ⟨fun i j => ?_, ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, map_add (f := _), hT, Matrix.single_apply, Matrix.single_apply]
      congr 1
      split_ifs with h1 h2 h2 <;> first | exact AlgEquiv.commutes σ c | exact map_zero σ | (exfalso; tauto)
    · rw [det_corOne T i₀ hr]
      exact (isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hc0)).mul hu0
  have hN : ∀ c : k, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K //
      ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K c)} =
      Nat.card {X : Fin (a' + 1) → Fin M → K //
        ffGram (σ : K →+* K) J X = T + Matrix.single i₀ i₀ (algebraMap k K 1)} := by
    intro c hc0
    have e1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt c hc0).1 (hTt c hc0).2
    have e2 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
      (hTt 1 one_ne_zero).2
    exact_mod_cast e1.trans e2.symm
  have hD : ∀ Y : Fin a' → Fin M → K, ffGram (σ : K →+* K) J Y = T.submatrix i₀.succAbove i₀.succAbove →
      Nat.card {x : Fin M → K // (∀ j, ffH (σ : K →+* K) J (Y j) x = 0) ∧ ffH (σ : K →+* K) J x x = 0 ∧
        ¬ ∀ c : K, c • x = 0 → c = 0} = 1 := by
    intro Y _
    rw [Nat.card_eq_one_iff_unique]
    have h0 : ∀ z : Fin M → K, ¬ (∀ c : K, c • z = 0 → c = 0) → z = 0 := fun z hz => by
      by_contra h0
      exact hz (fun c hc => (smul_eq_zero.1 hc).resolve_right h0)
    refine ⟨⟨fun x y => Subtype.ext ((h0 x.1 x.2.2.2).trans (h0 y.1 y.2.2.2).symm)⟩, ⟨⟨0, ?_⟩⟩⟩
    exact ⟨fun j => ffH_zero_right _ _ _, ffH_zero_left _ _ _, fun h => one_ne_zero (h 1 (smul_zero 1))⟩
  have hcnt := count_gen (σ : K →+* K) J hσ' hJ' T i₀ hr hc hu (by omega) (ι := algebraMap k K)
    (algebraMap k K).injective (map_zero _)
    (fun x => fixed_mem_range σ h2 hne _ (ffH_herm (σ : K →+* K) J hσ' hJ' x x).symm) _ 1 hN hD
  have hF0 := fFInert2_holds k K σ hσ h2 hne M a' (by omega) J hJ hdJ
    (T.submatrix i₀.succAbove i₀.succAbove) (fun i j => hT _ _) hu0
  have hN1 := fFInert2_holds k K σ hσ h2 hne M (a' + 1) haM J hJ hdJ _ (hTt 1 one_ne_zero).1
    (hTt 1 one_ne_zero).2
  have h1k : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hKk : Nat.card K = Nat.card k ^ 2 := by simp only [Nat.card_eq_fintype_card]; exact hK
  rw [hKk] at hcnt
  have hR := congrArg (fun n : ℕ => (n : ℝ)) hcnt
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h1k, Nat.cast_one] at hR
  rw [hF0, hN1] at hR
  have hx : (Nat.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [prodInert_closed _ hx M a' (by omega), prodInert_closed _ hx M (a' + 1) haM] at hR
  obtain ⟨n, hn⟩ : ∃ n, M = a' + 1 + n := ⟨M - (a' + 1), by omega⟩
  have eE : 2 * M * (a' + 1) - (a' + 1) ^ 2 = (2 * M * a' - a' ^ 2) + (2 * n + 1) := by
    subst hn
    have h3 : a' ^ 2 ≤ 2 * (a' + 1 + n) * a' := by nlinarith
    have h4 : (a' + 1) ^ 2 ≤ 2 * (a' + 1 + n) * (a' + 1) := by nlinarith
    zify [h3, h4]
    ring
  have i1 : Finset.Icc (M - (a' + 1) + 1) M = insert (n + 1) (Finset.Icc (n + 2) M) := by
    rw [show M - (a' + 1) + 1 = n + 1 by omega]
    exact (Finset.insert_Icc_add_one_left_eq_Icc (by omega)).symm
  have i0 : Finset.Icc (M - (a' + 1)) M = insert n (insert (n + 1) (Finset.Icc (n + 2) M)) := by
    rw [show M - (a' + 1) = n by omega, ← Finset.insert_Icc_add_one_left_eq_Icc (show n ≤ M by omega),
      ← Finset.insert_Icc_add_one_left_eq_Icc (show n + 1 ≤ M by omega)]
    rfl
  rw [show M - a' + 1 = n + 2 by omega, show M - a' = n + 1 by omega, eE, pow_add, i1,
    Finset.prod_insert (by simp)] at hR
  rw [eE, pow_add, i0, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  set P0 := ∏ j ∈ Finset.Icc (n + 2) M, (1 - (-1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))
  set x := (Nat.card k : ℝ)
  set E0 := 2 * M * a' - a' ^ 2
  linear_combination hR + (x ^ E0 * P0) * keyInert x hx n

end PI.OmVe
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.DcountSplit

section

@[expose] public section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

theorem keySplit (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - (2 * x ^ (n + 1) - 1) - (x - 1) * (x ^ (2 * n + 1) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - x ^ (-(n : ℤ))) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  field_simp
  ring

theorem dcount_split {k : Type} [Field k] [Finite k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k)) {a' : ℕ}
    (haM : a' ≤ M) (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0} + 1 =
      2 * Nat.card k ^ (M - a') := by
  classical
  have := Fintype.ofFinite k
  have hk0 : 0 < Nat.card k := Nat.card_pos
  have e2 : Nat.card k ^ M = Nat.card k ^ (M - a') * Nat.card k ^ a' := by
    rw [← pow_add, Nat.sub_add_cancel haM]
  have h1 := card_half_snd J T0 hu Y hY
  have h2 := card_half_fst J T0 hu Y hY
  rw [e2] at h1 h2
  have c1 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h1
  have c2 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h2
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at c1 c2 ⊢
  set s1 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0)
  set s2 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0)
  have hs : Finset.univ.filter (fun x : Fin M → k × k =>
      (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0) =
      s1 ∪ s2 := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rw [notFree_iff]
    constructor
    · rintro ⟨hP, _, h | h⟩
      · exact Or.inr ⟨hP, h⟩
      · exact Or.inl ⟨hP, h⟩
    · rintro (⟨hP, h⟩ | ⟨hP, h⟩)
      · exact ⟨hP, ffH_self_of_snd J x h, Or.inr h⟩
      · exact ⟨hP, ffH_self_of_fst J x h, Or.inl h⟩
  have hi : s1 ∩ s2 = {0} := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h2⟩, ⟨_, h1⟩⟩
      funext l; exact Prod.ext (h1 l) (h2 l)
    · rintro rfl
      exact ⟨⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩, ⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩⟩
  have hu2 := Finset.card_union_add_card_inter s1 s2
  rw [hi, Finset.card_singleton, c1, c2] at hu2
  rw [hs, hu2]
  ring

end PI.OmVe
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFSplitBHolds

section

@[expose] public section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

theorem fFSplitB_holds : PI.OmVd.FFSplitB := by
  intro k _ _ M a haM J hJ hJdet T hT hcor
  obtain ⟨i₀, hrow, hcol, hunit⟩ := hcor
  cases a with
  | zero => exact i₀.elim0
  | succ a' =>
    have hσ : ∀ x : k × k, RingEquiv.prodComm.toRingHom x = x.swap := fun x => rfl
    have hsub : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det := by
      have := PI.OmVe.det_corOne T i₀ hrow 1
      rw [this, one_mul] at hunit
      exact hunit
    have hinv : ∀ x : k × k, RingEquiv.prodComm.toRingHom (RingEquiv.prodComm.toRingHom x) = x := fun x => by simp [hσ]
    have hJ' : ∀ i j, RingEquiv.prodComm.toRingHom (J j i) = J i j := fun i j => by rw [hσ]; exact hJ i j
    have hdiag : ∀ x : Fin M → k × k, ∃ c : k, PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x = (c, c) := by
      intro x
      have h := PI.OmVe.ffH_herm RingEquiv.prodComm.toRingHom J hinv hJ' x x
      refine ⟨(PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x).1, ?_⟩
      rw [hσ] at h
      ext
      · rfl
      · exact (congrArg Prod.fst h).symm.trans rfl
    have hTs : ∀ i j, ((T.submatrix i₀.succAbove i₀.succAbove) j i).swap = (T.submatrix i₀.succAbove i₀.succAbove) i j := fun i j => hT _ _
    have hY := PI.VolStabSW.fFSplit_holds k M a' (by omega) J hJ hJdet _ hTs hsub
    have hNr : ∀ c : k, c ≠ 0 → (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ (c, c) } : ℝ) = (∏ i : Fin (a' + 1), ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) * (Nat.card k : ℝ) ^ ((a' + 1) * (M - (a' + 1))) := by
      intro c hc
      have hdet : IsUnit (T + Matrix.single i₀ i₀ (c, c)).det := by
        rw [PI.OmVe.det_corOne T i₀ hrow]
        refine IsUnit.mul ?_ hsub
        exact (Prod.isUnit_iff).2 ⟨isUnit_iff_ne_zero.2 hc, isUnit_iff_ne_zero.2 hc⟩
      have hh : ∀ i j, ((T + Matrix.single i₀ i₀ (c, c)) j i).swap = (T + Matrix.single i₀ i₀ (c, c)) i j := by
        intro i j
        rw [Matrix.add_apply, Matrix.add_apply, ← hT i j, Matrix.single_apply, Matrix.single_apply]
        by_cases h1 : i₀ = i <;> by_cases h2 : i₀ = j <;> ext <;> simp [h1, h2] <;> split_ifs <;> rfl
      exact PI.VolStabSW.fFSplit_holds k M (a' + 1) haM J hJ hJdet _ hh hdet
    have key := PI.OmVe.count_gen RingEquiv.prodComm.toRingHom J hinv hJ' T i₀ hrow hcol hunit (by omega) (k := k) (fun c => (c, c)) (fun c d h => by simpa using congrArg Prod.fst h) rfl
    specialize key hdiag
    clear hinv hJ' hdiag hσ
    have hk1 : 1 ≤ Nat.card k := Nat.card_pos
    have hk := key (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ ((1 : k), (1 : k)) }) (2 * Nat.card k ^ (M - a') - 1)
      (fun c hc => Nat.cast_injective (R := ℝ) ((hNr c hc).trans (hNr 1 one_ne_zero).symm))
      (fun Y hY' => by
        have := PI.OmVe.dcount_split J (by omega) _ hsub Y hY'
        have : 1 ≤ Nat.card k ^ (M - a') := Nat.one_le_pow _ _ hk1
        omega)
    have hN1 := hNr 1 one_ne_zero
    clear key hNr
    rw [Nat.card_prod] at hk
    have hkR := congrArg (fun n : ℕ => (n : ℝ)) hk
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk1, Nat.cast_one] at hkR
    rw [Nat.cast_sub (by have : 1 ≤ Nat.card k ^ (M - a') := Nat.one_le_pow _ _ hk1; omega)] at hkR
    rw [hY, hN1] at hkR
    push_cast at hkR
    have hq : (1 : ℝ) ≤ Nat.card k := by exact_mod_cast hk1
    generalize ((Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T ∧ LinearIndependent (k × k) X } : ℕ) : ℝ) = C at hkR ⊢
    generalize (Nat.card k : ℝ) = q at hkR hq ⊢
    clear hk hY hN1 hTs hsub hunit hrow hcol hT hJdet hJ
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le haM
    clear haM T J i₀
    have hq0 : q ≠ 0 := by positivity
    have e1 : a' + 1 + r - a' = r + 1 := by omega
    have e2 : a' + 1 + r - (a' + 1) = r := by omega
    have e3 : 2 * (a' + 1 + r) * (a' + 1) - (a' + 1) ^ 2 = (a' + 1) ^ 2 + 2 * r * (a' + 1) := Nat.sub_eq_of_eq_add (by ring)
    have hP := PI.OmVe.prodSplit_closed q hq0 (a' + 1 + r) a' (by omega)
    rw [e1] at hP hkR
    rw [e2] at hkR
    rw [e2, e3]
    simp only [one_pow, one_mul]
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r ≤ a' + 1 + r), Finset.prod_insert (by simp), ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r + 1 ≤ a' + 1 + r), Finset.prod_insert (by simp)]
    rw [Fin.prod_univ_castSucc] at hkR
    simp only [Fin.coe_castSucc, Fin.val_last] at hkR
    rw [hP] at hkR
    have hK := PI.OmVe.keySplit q hq0 r
    have e : q ^ (2 * r + 1) * (1 - q ^ (-((r + 1 : ℕ) : ℤ))) = (q ^ (r + 1) - 1) * q ^ r := by
      rw [_root_.zpow_neg, zpow_natCast]
      field_simp
      ring
    generalize (∏ j ∈ Finset.Icc (r + 1 + 1) (a' + 1 + r), (1 - q ^ (-(j : ℤ)))) = Pi' at hkR ⊢
    generalize (1 - q ^ (-((r + 1 : ℕ) : ℤ))) = B at hK e ⊢
    generalize (1 - q ^ (-(r : ℤ))) = A at hK ⊢
    linear_combination hkR + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1))) * hK + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1)) * (q - 1)) * e

end PI.OmVe
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertBHolds

section

@[expose] public section

namespace PI.OmVe.Top

theorem fFInertB_holds : PI.OmVd.FFInertB := PI.OmVe.fFInertB_holds

theorem fFSplitB_holds : PI.OmVd.FFSplitB := PI.OmVe.fFSplitB_holds

end PI.OmVe.Top
end
end

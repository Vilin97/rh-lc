module

public import Formalism.SuccessiveMinima.StatementMink
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.AdaptedBasis
public import Formalism.SuccessiveMinima.DefsMink
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
public import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjScale
public import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Basify
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.SuccMin

-- Source module: Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjLevel

section

@[expose] public section

open MeasureTheory Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

lemma measurableSet_boxJ (n j : ℕ) : MeasurableSet (boxJ n j) := by
  have h : boxJ n j = ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < j),
      ({u : Fin n → ℝ | 0 ≤ u i} ∩ {u | u i < 1}) := by
    ext u; simp [boxJ]
  rw [h]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem partialBoxVolumeMonotoneStep : GjLevel := by
  intro n j A hj hA hinj
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin n, (jj : ℕ) = j := ⟨⟨j, hj⟩, rfl⟩
  let ej : Fin n → ℝ := Pi.single jj 1
  have ej_apply : ∀ i, ej i = if i = jj then 1 else 0 := fun i => by simp [ej, Pi.single_apply]
  have hcoord : ∀ (y : Fin n → ℝ) (m : ℤ) (i : Fin n),
      (y + (m : ℝ) • ej) i = if i = jj then y i + m else y i := by
    intro y m i
    simp only [Pi.add_apply, Pi.smul_apply, ej_apply, smul_eq_mul]
    split_ifs <;> ring

  let S : Set (Fin n → ℝ) := boxJ n j ∩ (A + latJ n j)
  let P : ℤ → Set (Fin n → ℝ) := fun m => S ∩ {x | ⌊x jj⌋ = m}
  let Q : ℤ → Set (Fin n → ℝ) := fun m => (fun y => y + (m : ℝ) • ej) ⁻¹' P m
  have hSm : MeasurableSet S := (measurableSet_boxJ n j).inter (hA.add_right (t := latJ n j)).measurableSet
  have hPm : ∀ m, MeasurableSet (P m) := fun m =>
    hSm.inter ((Int.measurable_floor.comp (measurable_pi_apply jj)) (measurableSet_singleton m))
  have hQm : ∀ m, MeasurableSet (Q m) := fun m => (measurable_id.add_const _) (hPm m)
  have hvol : ∀ m, volume (Q m) = volume (P m) := fun m =>
    measure_preimage_add_right volume _ (P m)
  have hsub : ∀ m, Q m ⊆ boxJ n (j + 1) ∩ (A + latJ n (j + 1)) := by
    intro m y hy
    obtain ⟨⟨hbox, hAk⟩, hfl⟩ := hy
    have hfl' : ⌊(y + (m : ℝ) • ej) jj⌋ = m := hfl
    rw [hcoord, if_pos rfl, Int.floor_add_intCast] at hfl'
    have h0 : ⌊y jj⌋ = 0 := by omega
    have hyj := Int.floor_eq_zero_iff.1 h0
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases hij : i = jj
      · subst hij; exact ⟨hyj.1, hyj.2⟩
      · have hlt : (i : ℕ) < j :=
          lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) (fun h => hij (Fin.ext (h.trans hjj.symm)))
        have hb : 0 ≤ (y + (m : ℝ) • ej) i ∧ (y + (m : ℝ) • ej) i < 1 := hbox i hlt
        rw [hcoord, if_neg hij] at hb
        exact hb
    · obtain ⟨a, ha, k, hk, hak0⟩ := hAk
      have hak : a + k = y + (m : ℝ) • ej := hak0
      refine Set.mem_add.2 ⟨a, ha, k - (m : ℝ) • ej, ⟨?_, ?_⟩, ?_⟩
      · intro i
        obtain ⟨z, hz⟩ := hk.1 i
        refine ⟨z - (if i = jj then m else 0), ?_⟩
        simp only [Pi.sub_apply, Pi.smul_apply, ej_apply, smul_eq_mul, hz]
        split_ifs <;> push_cast <;> ring
      · intro i hi
        have hne : i ≠ jj := fun h => by rw [h, hjj] at hi; omega
        simp [hk.2 i (by omega), ej_apply, hne]
      · rw [← add_sub_assoc, hak, add_sub_cancel_right]
  have hdisj : Pairwise (Function.onFun Disjoint Q) := by
    intro m m' hmm'
    rw [Function.onFun, Set.disjoint_left]
    intro y hy hy'
    obtain ⟨⟨_, hAk⟩, _⟩ := hy
    obtain ⟨⟨_, hAk'⟩, _⟩ := hy'
    obtain ⟨a, ha, k, hk, hak0⟩ := hAk
    obtain ⟨a', ha', k', hk', hak0'⟩ := hAk'
    have hak : a + k = y + (m : ℝ) • ej := hak0
    have hak' : a' + k' = y + (m' : ℝ) • ej := hak0'
    have hint : ∀ i, ∃ z : ℤ, a i - a' i = z := by
      intro i
      obtain ⟨z, hz⟩ := hk.1 i
      obtain ⟨z', hz'⟩ := hk'.1 i
      have e1 := congrFun hak i
      have e2 := congrFun hak' i
      rw [Pi.add_apply, hcoord] at e1 e2
      split_ifs at e1 e2
      · exact ⟨m - m' - z + z', by push_cast; linarith⟩
      · exact ⟨-z + z', by push_cast; linarith⟩
    have hjeq := hinj a ha a' ha' hint jj hjj.ge
    have hk0 : k jj = 0 := hk.2 jj hjj.ge
    have hk0' : k' jj = 0 := hk'.2 jj hjj.ge
    have e1 := congrFun hak jj
    have e2 := congrFun hak' jj
    rw [Pi.add_apply, hcoord, if_pos rfl, hk0, add_zero] at e1
    rw [Pi.add_apply, hcoord, if_pos rfl, hk0', add_zero] at e2
    apply hmm'
    exact_mod_cast (by linarith : (m : ℝ) = m')
  have hcover : S ⊆ ⋃ m : ℤ, P m := fun x hx => Set.mem_iUnion.2 ⟨⌊x jj⌋, hx, rfl⟩
  calc Gj n j A = volume S := rfl
    _ ≤ volume (⋃ m : ℤ, P m) := measure_mono hcover
    _ ≤ ∑' m, volume (P m) := measure_iUnion_le _
    _ = ∑' m, volume (Q m) := tsum_congr fun m => (hvol m).symm
    _ = volume (⋃ m, Q m) := (measure_iUnion hdisj hQm).symm
    _ ≤ volume (boxJ n (j + 1) ∩ (A + latJ n (j + 1))) := measure_mono (Set.iUnion_subset hsub)
    _ = Gj n (j + 1) A := rfl

end Formalism.FN
end
end
end

-- Source module: Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MeasureEqCovolumeMulVolumeImage

section

@[expose] public section

open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

theorem measure_eq_covolume_mul_volume_image {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type} [Fintype ι] (b : Basis ι ℤ L) (S : Set E) :
    μ S = ENNReal.ofReal (ZLattice.covolume L μ) *
      volume ((b.ofZLatticeBasis ℝ L).equivFun '' S) := by
  set B := b.ofZLatticeBasis ℝ L with hB
  let f : E ≃ᵐ (ι → ℝ) := B.equivFunL.toHomeomorph.toMeasurableEquiv
  have hf : (f : E → ι → ℝ) = B.equivFun := rfl
  have : (μ.map f).IsAddHaarMeasure := B.equivFunL.isAddHaarMeasure_map μ
  have huniq := MeasureTheory.Measure.isAddLeftInvariant_eq_smul (μ.map f) volume
  obtain ⟨c, hc⟩ : ∃ c, c = MeasureTheory.Measure.addHaarScalarFactor (μ.map f) volume := ⟨_, rfl⟩
  rw [← hc] at huniq
  have himg : ∀ T : Set E, μ T = c * volume (B.equivFun '' T) := by
    intro T
    have h1 : μ T = μ.map f (f '' T) := by
      rw [MeasurableEquiv.map_apply, Set.preimage_image_eq T f.injective]
    rw [h1, huniq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hf]
  have hD : (B.equivFun : E → ι → ℝ) '' ZSpan.fundamentalDomain B =
      Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1 := by
    have h : ZSpan.fundamentalDomain B =
        (B.equivFun : E → ι → ℝ) ⁻¹' (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) := by
      ext x
      simp [ZSpan.mem_fundamentalDomain, Set.mem_pi]
    rw [h, Set.image_preimage_eq _ B.equivFun.surjective]
  have hvol : volume (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]
    simp
  have hcov : c = ENNReal.ofReal (ZLattice.covolume L μ) := by
    have h := himg (ZSpan.fundamentalDomain B)
    rw [hD, hvol, mul_one] at h
    rw [← h, ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ),
      measureReal_def, ENNReal.ofReal_toReal]
    exact (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded B)).ne
  rw [himg S, hcov]

theorem minkowskiIIUpper_of (hc : MinkCore) (hs : SuccMinFacts) (ha : AdaptedBasis) :
    MinkowskiIIUpper := by
  intro E _ _ _ _ _ μ _ L _ _ K hKc hKconv hKsymm hK0
  obtain ⟨v, hvli, hvL, hvK, hpos, hmono, hspan⟩ := hs L K hKc hKconv hKsymm hK0
  obtain ⟨b, hb⟩ := ha L v hvli hvL
  set B := b.ofZLatticeBasis ℝ L with hB
  have hBfun : ∀ i, B i = (b i : E) := fun i => by simp [hB]
  set lam : Fin (finrank ℝ E) → ℝ := fun i => succMin L K ((i : ℕ) + 1) with hlam
  have hneg : ∀ a ∈ interior K, -a ∈ interior K := by
    intro a ha'
    have hU : IsOpen ((fun x : E => -x) ⁻¹' interior K) := isOpen_interior.preimage continuous_neg
    have hsub : (fun x : E => -x) ⁻¹' interior K ⊆ K := fun x hx => by
      simpa using hKsymm _ (interior_subset hx)
    exact interior_maximal hsub hU (by simpa using ha')
  have hCo : IsOpen (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    B.equivFunL.toHomeomorph.isOpenMap _ (isOpen_interior.smul₀ (by norm_num))
  have hCc : Convex ℝ (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    (hKconv.interior.smul (1 / 2 : ℝ)).linear_image B.equivFun.toLinearMap
  have hCs : ∀ x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K),
      -x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Set.mem_smul_set] at hw
    obtain ⟨a, ha', rfl⟩ := hw
    exact ⟨(1 / 2 : ℝ) • -a, Set.smul_mem_smul_set (hneg a ha'), by rw [smul_neg, map_neg]⟩
  have hCb : Bornology.IsBounded (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    B.equivFunL.lipschitzWith.isBounded_image ((hKc.isBounded.subset interior_subset).smul₀ _)
  have key := hc (finrank ℝ E) (B.equivFun '' ((1 / 2 : ℝ) • interior K)) lam hCo hCc hCs hCb
    hpos hmono (by
      intro j x hx y hy hint i hji
      rw [Set.mem_smul_set] at hx hy
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hx
      obtain ⟨_, ⟨w', hw', rfl⟩, rfl⟩ := hy
      rw [Set.mem_smul_set] at hw hw'
      obtain ⟨a, ha', rfl⟩ := hw
      obtain ⟨a', ha'', rfl⟩ := hw'
      obtain ⟨u, hu⟩ : ∃ u, u = lam j • ((1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a') := ⟨_, rfl⟩
      have heu : B.equivFun u =
          lam j • B.equivFun ((1 / 2 : ℝ) • a) - lam j • B.equivFun ((1 / 2 : ℝ) • a') := by
        rw [hu, map_smul B.equivFun (lam j), map_sub, smul_sub]
      have hrepr : ∀ i, B.repr u i =
          (lam j • B.equivFun ((1 / 2 : ℝ) • a)) i - (lam j • B.equivFun ((1 / 2 : ℝ) • a')) i := by
        intro i
        have h := congrFun heu i
        rw [B.equivFun_apply] at h
        exact h
      have huL : u ∈ L := by
        rw [← B.sum_repr u]
        refine sum_mem fun i _ => ?_
        obtain ⟨m, hm⟩ := hint i
        rw [hrepr i, hm, hBfun i]
        rw [Int.cast_smul_eq_zsmul ℝ m]
        exact L.smul_mem m (b i).2
      have hmid : (1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a' ∈ interior K := by
        rw [sub_eq_add_neg, ← smul_neg]
        exact hKconv.interior ha' (hneg a' ha'') (by norm_num) (by norm_num) (by norm_num)
      have hmem : u ∈ Submodule.span ℝ (v '' {k | k < j}) :=
        hspan j u huL (by rw [hu]; exact Set.smul_mem_smul_set hmid)
      have hsub : Submodule.span ℝ (v '' {k | k < j}) ≤ Submodule.span ℝ (B '' {k | k < j}) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        have h1 : v k ∈ Submodule.span ℝ (v '' {k' | k' ≤ k}) :=
          Submodule.subset_span ⟨k, le_refl k, rfl⟩
        rw [← hb k] at h1
        refine Submodule.span_mono ?_ h1
        rintro _ ⟨k', hk', rfl⟩
        exact ⟨k', show k' < j from lt_of_le_of_lt hk' hk, hBfun k'⟩
      have hsupp := (B.mem_span_image).mp (hsub hmem)
      have hz : B.repr u i = 0 := by
        by_contra h
        exact absurd (hsupp (Finsupp.mem_support_iff.mpr h)) (not_lt.mpr hji)
      have h0 := hrepr i
      rw [hz] at h0
      exact sub_eq_zero.mp h0.symm)
  have hthm := measure_eq_covolume_mul_volume_image μ L b ((1 / 2 : ℝ) • interior K)
  rw [← hB] at hthm
  have hhalf : μ ((1 / 2 : ℝ) • interior K) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ finrank ℝ E) * μ (interior K) := by
    rw [Measure.addHaar_smul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ finrank ℝ E)]
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hIfin : μ (interior K) < ⊤ := lt_of_le_of_lt (measure_mono interior_subset) hKfin
  have hKle : μ K ≤ μ (interior K) := by
    calc μ K ≤ μ (interior K ∪ frontier K) := by
          apply measure_mono
          intro x hx
          rw [← closure_eq_interior_union_frontier]
          exact subset_closure hx
      _ ≤ μ (interior K) + μ (frontier K) := measure_union_le _ _
      _ = μ (interior K) := by rw [hKconv.addHaar_frontier μ, add_zero]
  have hP : 0 ≤ ∏ i, lam i := Finset.prod_nonneg fun i _ => (hpos i).le
  have hc0 : 0 ≤ ZLattice.covolume L μ := (ZLattice.covolume_pos L μ).le
  have e1 : (μ ((1 / 2 : ℝ) • interior K)).toReal =
      ZLattice.covolume L μ * (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal := by
    rw [hthm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]
  have e2 : (μ ((1 / 2 : ℝ) • interior K)).toReal =
      (1 / 2 : ℝ) ^ finrank ℝ E * (μ (interior K)).toReal := by
    rw [hhalf, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have e3 : (μ (interior K)).toReal = 2 ^ finrank ℝ E * (ZLattice.covolume L μ *
      (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal) := by
    have h2 : (2 : ℝ) ^ finrank ℝ E * (1 / 2 : ℝ) ^ finrank ℝ E = 1 := by
      rw [← mul_pow]
      norm_num
    calc (μ (interior K)).toReal
        = 2 ^ finrank ℝ E * ((1 / 2 : ℝ) ^ finrank ℝ E * (μ (interior K)).toReal) := by
          rw [← mul_assoc, h2, one_mul]
      _ = _ := by rw [← e2, e1]
  have hK' : μ.real K ≤ (μ (interior K)).toReal := ENNReal.toReal_mono hIfin.ne hKle
  calc μ.real K * ∏ i, lam i ≤ (μ (interior K)).toReal * ∏ i, lam i :=
        mul_le_mul_of_nonneg_right hK' hP
    _ = 2 ^ finrank ℝ E * ZLattice.covolume L μ *
        ((volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal * ∏ i, lam i) := by
          rw [e3]
          ring
    _ ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ * 1 :=
        mul_le_mul_of_nonneg_left key (mul_nonneg (by positivity) hc0)
    _ = _ := mul_one _

end Formalism.FN
end
end
end

-- Source module: Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkCore

section

@[expose] public section

open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

theorem partialBoxVolumeTopLeOne : GjTop := by
  intro n A
  unfold Gj
  calc volume (boxJ n n ∩ (A + latJ n n)) ≤ volume (boxJ n n) :=
        measure_mono Set.inter_subset_left
    _ ≤ volume (Set.univ.pi fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
        apply measure_mono
        intro u hu i _
        exact hu i i.2
    _ = 1 := by
        rw [Real.volume_pi_Ico]
        simp

theorem gjZero (n : ℕ) (A : Set (Fin n → ℝ)) : Gj n 0 A = volume A := by
  unfold Gj
  have h1 : boxJ n 0 = Set.univ := by
    ext u
    simp [boxJ]
  have h2 : latJ n 0 = {0} := by
    ext k
    simp only [latJ, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, hk⟩
      funext i
      exact hk i (Nat.zero_le _)
    · rintro rfl
      exact ⟨fun _ => ⟨0, by simp⟩, fun _ _ => rfl⟩
  rw [h1, h2, Set.univ_inter]
  simp

theorem minkCore_of (h3 : GjLevel) (h4 : GjScale) : MinkCore := by
  intro n C lam hCo hCc hCs hCb hpos hmono hsep
  have hsmulC : ∀ k : Fin n, IsOpen (lam k • C) := fun k => hCo.smul₀ (hpos k).ne'
  have hlev : ∀ k : Fin n, Gj n k (lam k • C) ≤ Gj n (k + 1) (lam k • C) := by
    intro k
    apply h3 n k (lam k • C) k.2 (hsmulC k)
    intro x hx y hy hxy i hi
    exact hsep k x hx y hy hxy i (Fin.le_def.mpr hi)
  have hbase : ∀ hk : 0 < n, ENNReal.ofReal (∏ i, min (lam i) (lam ⟨0, hk⟩)) * volume C
      ≤ Gj n 0 (lam ⟨0, hk⟩ • C) := by
    intro hk
    rw [gjZero, Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos (hpos _) n)]
    have e : ∏ i, min (lam i) (lam ⟨0, hk⟩) = lam ⟨0, hk⟩ ^ n := by
      rw [Finset.prod_congr rfl
        (fun i _ => min_eq_right (hmono (show (⟨0, hk⟩ : Fin n) ≤ i from
          Fin.le_def.mpr (Nat.zero_le (i : ℕ)))))]
      simp
    rw [e]
  have hstep : ∀ k (hk0 : k < n) (hk : k + 1 < n),
      ∏ i, min (lam i) (lam ⟨k + 1, hk⟩) =
        (lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1)) * ∏ i, min (lam i) (lam ⟨k, hk0⟩) := by
    intro k hk0 hk
    have hab : lam ⟨k, hk0⟩ ≤ lam ⟨k + 1, hk⟩ := hmono (Fin.mk_le_mk.mpr (by omega))
    have ha0 : 0 < lam ⟨k, hk0⟩ := hpos _
    have hfac : ∀ i : Fin n, min (lam i) (lam ⟨k + 1, hk⟩) =
        (if k < (i : ℕ) then lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩ else 1) * min (lam i) (lam ⟨k, hk0⟩) := by
      intro i
      split_ifs with h
      · have h1 : lam ⟨k + 1, hk⟩ ≤ lam i := hmono (Fin.le_def.mpr (show k + 1 ≤ (i : ℕ) by omega))
        rw [min_eq_right h1, min_eq_right (hab.trans h1), div_mul_cancel₀ _ ha0.ne']
      · have h1 : lam i ≤ lam ⟨k, hk0⟩ := hmono (Fin.le_def.mpr (show (i : ℕ) ≤ k by omega))
        rw [min_eq_left (h1.trans hab), min_eq_left h1, one_mul]
    have hcard : (Finset.univ.filter fun i : Fin n => k < (i : ℕ)).card = n - (k + 1) := by
      have e : (Finset.univ.filter fun i : Fin n => k < (i : ℕ)) = Finset.Ioi ⟨k, hk0⟩ := by
        ext i
        simp [Fin.lt_def]
      rw [e, Fin.card_Ioi]
      simp only
      omega
    rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib, Finset.prod_ite,
      Finset.prod_const, Finset.prod_const_one, mul_one, hcard]
  have claim : ∀ k (hk : k < n), ENNReal.ofReal (∏ i, min (lam i) (lam ⟨k, hk⟩)) * volume C
      ≤ Gj n k (lam ⟨k, hk⟩ • C) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      intro hk
      have hk0 : k < n := by omega
      have hr : 0 ≤ (lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1)) := by
        have := hpos ⟨k + 1, hk⟩
        have := hpos ⟨k, hk0⟩
        positivity
      rw [hstep k hk0 hk, ENNReal.ofReal_mul hr, mul_assoc]
      calc ENNReal.ofReal ((lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1))) *
            (ENNReal.ofReal (∏ i, min (lam i) (lam ⟨k, hk0⟩)) * volume C)
          ≤ ENNReal.ofReal ((lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1))) *
            Gj n (k + 1) (lam ⟨k, hk0⟩ • C) := by
            gcongr
            exact (ih hk0).trans (hlev ⟨k, hk0⟩)
        _ ≤ Gj n (k + 1) (lam ⟨k + 1, hk⟩ • C) :=
            h4 n (k + 1) C (lam ⟨k, hk0⟩) (lam ⟨k + 1, hk⟩) hk.le hCo hCc hCs hCb (hpos _)
              (hmono (Fin.mk_le_mk.mpr (by omega)))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 := partialBoxVolumeTopLeOne 0 C
    rw [gjZero] at h0
    simp only [Fin.prod_univ_zero, mul_one]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h0)
  · have hn1 : n - 1 < n := by omega
    have hlast := (claim (n - 1) hn1).trans (hlev ⟨n - 1, hn1⟩)
    have htop := partialBoxVolumeTopLeOne n (lam ⟨n - 1, hn1⟩ • C)
    have e : ((⟨n - 1, hn1⟩ : Fin n) : ℕ) + 1 = n := by
      show n - 1 + 1 = n
      omega
    rw [e] at hlast
    have hprod : ∏ i, min (lam i) (lam ⟨n - 1, hn1⟩) = ∏ i, lam i :=
      Finset.prod_congr rfl fun i _ =>
        min_eq_left (hmono (Fin.le_def.mpr (show (i : ℕ) ≤ n - 1 by omega)))
    rw [hprod] at hlast
    have hP : 0 ≤ ∏ i, lam i := Finset.prod_nonneg fun i _ => (hpos i).le
    have hfin : ENNReal.ofReal (∏ i, lam i) * volume C ≤ 1 := hlast.trans htop
    rw [mul_comm, ← ENNReal.toReal_ofReal hP, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hfin)

end Formalism.FN
end
end
end

-- Source module: Formalism.SuccessiveMinima.MinkowskiIIUpper

section

@[expose] public section

namespace Formalism.FN

theorem minkowskiIIUpper : MinkowskiIIUpper :=
  minkowskiIIUpper_of (minkCore_of partialBoxVolumeMonotoneStep partialBoxVolumeScaling) existsSuccessiveMinimaVectors
    existsAdaptedBasis

end Formalism.FN
end
end

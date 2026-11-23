module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPowerSeries.Basic
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OddSpanVariable

section

@[expose] public section

theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X :
    ∀ {O σ ι : Type} [inst : CommRing O] (e : ι → σ) (s : Finset ι)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ),
        (∀ i ∈ s, (n : σ → ℕ) (e i) = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range fun (i : ι) ↦ MvPowerSeries.X (e i)) := by
  intro O σ ι inst e s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a s _ ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n (e a) = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g
        = if n (e a) = 0 then MvPowerSeries.coeff n f else 0 := fun _ => rfl
    have h1 : g ∈ Ideal.span (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) := by
      refine ih g fun n hn => ?_
      rw [hg]
      split_ifs with h
      · refine hf n fun i hi => ?_
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X (e a) : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have h3 : f - g ∈ Ideal.span
        (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpOddSpanX

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ep_odd_span_X {O σ ι : Type} [CommRing O] (e : ι → σ) (s : Finset ι) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n (e i) = 0) → MvPowerSeries.coeff n f = 0) →
      f ∈ Ideal.span (Set.range fun i => (MvPowerSeries.X (e i) : MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X e s

theorem UpperTheory.V.Fr.ep_odd :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (P : GPres O σ), Ideal.span (evp σ 1 : Set R) = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (.inr i))) := by
  intro O _ _ R _ _ _ σ P
  classical
  rw [← P.part 1]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h1 : f ∈ Ideal.span (Set.range fun i : Fin P.g =>
        (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin P.a ⊕ Fin P.g) O)) := by
      refine ep_odd_span_X Sum.inr Finset.univ f fun n hn => hf n ?_
      have : Finsupp.weight (Space.Loc.par P.a P.g) n = 0 := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        refine Finset.sum_eq_zero fun s _ => ?_
        rcases s with s | s
        · simp [Space.Loc.par]
        · simp [hn s (Finset.mem_univ _)]
      rw [this]
      decide
    have h2 := Ideal.mem_map_of_mem P.p h1
    rw [Ideal.map_span, ← Set.range_comp] at h2
    exact h2
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine Ideal.subset_span ⟨MvPowerSeries.X (.inr i), fun n hn => ?_, rfl⟩
    rw [MvPowerSeries.coeff_X, if_neg]
    rintro rfl
    apply hn
    simp [Finsupp.weight_single, Space.Loc.par]
end
end

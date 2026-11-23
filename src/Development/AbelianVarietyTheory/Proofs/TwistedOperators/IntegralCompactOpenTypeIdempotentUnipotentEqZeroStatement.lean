module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Formalism.JacquetSubsetSums.JacquetSubsetSum
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRepSubgroupEqZero

section

@[expose] public section

noncomputable section

namespace GlobalTheory.NoFixedCharSum

theorem sum_rep_subgroup_eq_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N]
    (h : ∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) : ∑ n : N, τ (n : G) = 0 := by
  ext v
  simp only [LinearMap.sum_apply, LinearMap.zero_apply]
  apply h
  intro m hm

  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨m, hm⟩ : N)) _ _ ?_
  intro n
  simp [map_mul]

theorem noFixedSum : Formalism.PacketSums.NoFixedSum := by
  intro G V _ _ _ _ τ N _ h x y
  have h0 := sum_rep_subgroup_eq_zero τ N h
  have : ∑ n : N, τ (x * (n : G) * y) = τ x * (∑ n : N, τ (n : G)) * τ y := by
    simp [Finset.mul_sum, Finset.sum_mul, map_mul]

  rw [← map_sum, this, h0]
  simp

end GlobalTheory.NoFixedCharSum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompactOpenTypeIdempotentUnipotentEqZero

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.TypeIdemAverage

theorem integral_eq_zero_of_sum_translate {N ι : Type} [Group N] [MeasurableSpace N] [MeasurableMul N]
    (ν : Measure N) [ν.IsMulLeftInvariant] [Fintype ι] [Nonempty ι] (n : ι → N) (F : N → ℂ)
    (h : ∀ u, ∑ i, F (n i * u) = 0) : ∫ u, F u ∂ν = 0 := by
  by_cases hF : Integrable F ν
  · have h1 : ∫ u, ∑ i, F (n i * u) ∂ν = ∑ i, ∫ u, F (n i * u) ∂ν :=
      integral_finsetSum _ fun i _ => hF.comp_mul_left (n i)
    simp only [h, integral_zero, integral_mul_left_eq_self, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  · exact integral_undef hF

theorem sum_typeIdem_translate {G Q W : Type} [Group G] [MeasurableSpace G] (μ : Measure G) [Group Q]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {K : Subgroup G} (red : K →* Q)
    (τ : Representation ℂ Q W) (H : Subgroup Q) [Fintype H] (hH : NoFixed τ H) (κ : H → K)
    (hκ : ∀ v, red (κ v) = v) (g : G) : ∑ v, GlobalTheory.Orb.typeIdem μ red τ (κ v * g) = 0 := by
  by_cases hg : g ∈ K
  · obtain ⟨g, rfl⟩ : ∃ g' : K, (g' : G) = g := ⟨⟨g, hg⟩, rfl⟩
    have h0 := GlobalTheory.NoFixedCharSum.noFixedSum Q W τ H hH 1 (red g)
    simp only [← Subgroup.coe_mul, GlobalTheory.Orb.typeIdem_coe, map_mul red, hκ]

    rw [← Finset.mul_sum, ← map_sum]
    simp only [one_mul] at h0
    have h1 : ∑ v : H, τ.character ((v : Q) * red g) = 0 := h0
    rw [h1, map_zero, mul_zero]
  · refine Finset.sum_eq_zero fun v _ => GlobalTheory.Orb.typeIdem_of_notMem μ red τ ?_
    rwa [K.mul_mem_cancel_left (κ v).2]

theorem integral_idemGL_eq_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {r : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W)
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k))
    (N : Subgroup (GL (Fin r) k)) (ν : Measure N) [ν.IsMulLeftInvariant] (H : Subgroup (GL (Fin r) 𝓀[k]))
    (hH : NoFixed τ H) (x : GL (Fin r) k)
    (hx : ∀ v ∈ H, ∃ n ∈ N, ∃ hn : x * n * x⁻¹ ∈ KO k (Fin r),
      GlobalTheory.LocGL.redK k (Fin r) ⟨x * n * x⁻¹, hn⟩ = v)
    (w : GL (Fin r) k) : ∫ u : N, idemGL k μ τ (x * u * w) ∂ν = 0 := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  choose n hnN hnK hred using hx
  refine integral_eq_zero_of_sum_translate ν (fun v : H => (⟨n v v.2, hnN v v.2⟩ : N))
    (fun u : N => idemGL k μ τ (x * u * w)) fun u => ?_
  have h := sum_typeIdem_translate μ (GlobalTheory.LocGL.redK k (Fin r)) τ H hH
    (fun v => ⟨x * n v v.2 * x⁻¹, hnK v v.2⟩) (fun v => hred v v.2) (x * u * w)
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) h
  simp only [idemGL, Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left]

end GlobalTheory.TypeIdemAverage
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompactOpenTypeIdempotentUnipotentEqZeroStatement

section

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

theorem _root_.GlobalTheory.T.integral_compactOpenTypeIdempotent_unipotent_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W)
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k))
    (N : Subgroup (GL (Fin r) k)) (ν : Measure N) [ν.IsMulLeftInvariant] (H : Subgroup (GL (Fin r) 𝓀[k])),
    NoFixed τ H → ∀ x : GL (Fin r) k,
    (∀ v ∈ H, ∃ n ∈ N, ∃ hn : x * n * x⁻¹ ∈ KO k (Fin r), GlobalTheory.LocGL.redK k (Fin r) ⟨x * n * x⁻¹, hn⟩ = v) →
    ∀ w : GL (Fin r) k, ∫ u : N, idemGL k μ τ (x * u * w) ∂ν = 0 := by
  first | exact @GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero | exact GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero | (intros; apply GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero <;> assumption)
end
end

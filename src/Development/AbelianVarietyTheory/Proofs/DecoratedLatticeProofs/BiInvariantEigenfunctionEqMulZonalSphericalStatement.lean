module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceLocalFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceOrderStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetRepsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeSubsetSumStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalDoubleCosetRepsMulStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalOverDiagonalDoubleCosetReps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntBiInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitoneStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.exists_antitone_cartan_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), x = κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * κ' := by
  exact @GlobalTheory.SortedCartan.cartan_antitone
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalOverDiagonalDoubleCosetRepsStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.sum_borelSpherical_over_diagonalDoubleCosetReps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (s : Finset (Fin N)) (R : Finset (GL (Fin N) k)), IsRepsK (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (indic s)) R → ∑ g ∈ R, ψ g = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s.card, ((resCard k : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, γ a) := by
  first | exact @GlobalTheory.BorelCosetSum.sum_cosets_eq | exact GlobalTheory.BorelCosetSum.sum_cosets_eq | (intros; apply GlobalTheory.BorelCosetSum.sum_cosets_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntEig

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalEig

theorem zonalInt_eig : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ (R : Finset (GL (Fin N) k)) (c : ℂ), (∀ m, ∑ g ∈ R, ψ (m * g) = c * ψ m) → ∀ m, ∑ g ∈ R, zonalInt μK ψ (m * g) = c * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hμ ψ hψ R c hR m
  have hKo := (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N))
  have hcont : Continuous ψ := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_)
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k))) := hKo.preimage (by fun_prop)
    filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ (KO k (Fin N) : Set (GL (Fin N) k)) by
      rw [inv_mul_cancel]; exact one_mem _)] with x hx
    have := hψ g _ hx
    rwa [mul_inv_cancel_left] at this
  have hint : ∀ y, IntegrableOn (fun κ => ψ (κ * y)) (KO k (Fin N) : Set (GL (Fin N) k)) μK := fun y =>
    (hcont.comp (continuous_mul_const y)).continuousOn.integrableOn_compact GlobalTheory.SplitFlip.isCompact_KO
  simp only [zonalInt]
  rw [← integral_finsetSum _ (fun g _ => hint (m * g)), ← integral_const_mul]
  congr 1
  funext κ
  have := hR (κ * m)
  simpa only [mul_assoc] using this

end GlobalTheory.ZonalEig
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntEigStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.sum_zonalInt_mul_eq_of_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ (R : Finset (GL (Fin N) k)) (c : ℂ), (∀ m, ∑ g ∈ R, ψ (m * g) = c * ψ m) → ∀ m, ∑ g ∈ R, zonalInt μK ψ (m * g) = c * zonalInt μK ψ m := by
  first | exact @GlobalTheory.ZonalEig.zonalInt_eig | exact GlobalTheory.ZonalEig.zonalInt_eig | (intros; apply GlobalTheory.ZonalEig.zonalInt_eig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntOneEqOne

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalOne

theorem zonalInt_one_eq_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
    [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure] :
    μK (KO k (Fin N)) = 1 → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → zonalInt μK ψ 1 = 1 := by
  intro hK γ ψ hψ
  have h1 : ψ 1 = 1 := by
    rw [hψ.2 1 (one_mem _) (fun _ => 1) (fun i => by simp)]
    simp [ord]
  have hκ : ∀ κ ∈ (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * 1) = 1 := by
    intro κ hκ
    rw [mul_one, ← one_mul κ, hψ.1 1 κ hκ, h1]
  unfold zonalInt
  rw [setIntegral_congr_fun GlobalTheory.SplitFlip.isOpen_KO.measurableSet hκ]
  simp [Measure.real, hK]

end GlobalTheory.ZonalOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntOneEqOneStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.zonalInt_one_eq_one_of_isBorelSph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → zonalInt μK ψ 1 = 1 := by
  first | exact @GlobalTheory.ZonalOne.zonalInt_one_eq_one | exact GlobalTheory.ZonalOne.zonalInt_one_eq_one | (intros; apply GlobalTheory.ZonalOne.zonalInt_one_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiInvariantEigenfunctionEqMulZonalSpherical

section

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalUnique

theorem genVal_top_ne_zero (q N : ℕ) (α : Fin N → ℂˣ) : genVal q 0 N (Finset.univ.val.map α) N ≠ 0 := by
  simp only [genVal, Nat.sub_self, mul_zero, zero_mul, add_zero, pow_zero, one_mul, Multiset.map_map]
  have e : (Multiset.map ((fun b : ℂˣ => (b : ℂ)) ∘ α) Finset.univ.val).esymm N = ∏ i, (α i : ℂ) := by
    rw [Finset.esymm_map_val]
    have : (Finset.univ : Finset (Fin N)).powersetCard N = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin N))
    rw [this, Finset.sum_singleton]; rfl
  rw [e, Finset.prod_ne_zero_iff]
  exact fun i _ => (α i).ne_zero

theorem eq_mul_zonalInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ α : Fin N → ℂˣ, ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ ∧ ∀ f : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * f m) → ∀ m, f m = f 1 * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hK ϖ hϖ α
  have hq : (1 : ℕ) < resCard k := GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have hγ : ∀ i, borelParam (resCard k) α i ≠ 0 := by
    intro i
    unfold borelParam
    refine mul_ne_zero (α i).ne_zero ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by exact_mod_cast (show resCard k ≠ 0 by omega) (by exact_mod_cast h.1)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_borelSphericalFunction k N _ hγ
  refine ⟨ψ, hψ, fun f hf he m => ?_⟩
  have hr : ∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g := hψ.1
  have hωb := GlobalTheory.T.zonalInt_mul_KO_invariant k N μK hK ψ hr
  have hω1 := GlobalTheory.T.zonalInt_one_eq_one_of_isBorelSph k N μK hK _ ψ hψ
  have hωe : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, zonalInt μK ψ (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * zonalInt μK ψ m := by
    intro s R hR
    refine GlobalTheory.T.sum_zonalInt_mul_eq_of_eigen k N μK hK ψ hr R _ fun m => ?_
    rw [GlobalTheory.T.sum_borelSpherical_doubleCosetReps_mul k N _ ψ hψ hγ _ R hR m, GlobalTheory.T.sum_borelSpherical_over_diagonalDoubleCosetReps k N ϖ hϖ _ ψ hψ hγ s R hR,
      GlobalTheory.T.sum_powersetCard_borelParam_eq_genVal (resCard k) N (by omega) α s.card, mul_comm]
  have hcN : genVal (resCard k) 0 N (Finset.univ.val.map α) N ≠ 0 := genVal_top_ne_zero _ N α
  have key := GlobalTheory.T.cartan_decomposition_dominance_order k N ϖ (fun n => genVal (resCard k) 0 N (Finset.univ.val.map α) n) hcN
    (GlobalTheory.T.exists_antitone_cartan_decomposition k N ϖ hϖ) (GlobalTheory.T.cartan_decomposition_dominance_local_field k N ϖ hϖ) (fun g => (GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps k Unit (Fin N)).2 g)
    (fun m => f m - f 1 * zonalInt μK ψ m)
    (fun κ hκ m => ⟨by rw [(hf κ hκ m).1, (hωb κ hκ m).1], by rw [(hf κ hκ m).2, (hωb κ hκ m).2]⟩)
    (fun s R hR m => by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, he s R hR m, hωe s R hR m]
      ring)
    (by simp [hω1]) m
  exact sub_eq_zero.1 key

end GlobalTheory.ZonalUnique

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiInvariantEigenfunctionEqMulZonalSphericalStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.biInvariant_eigenfunction_eq_mul_zonalSpherical : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ α : Fin N → ℂˣ, ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ ∧ ∀ f : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * f m) → ∀ m, f m = f 1 * zonalInt μK ψ m := by
  first | exact @GlobalTheory.ZonalUnique.eq_mul_zonalInt | exact GlobalTheory.ZonalUnique.eq_mul_zonalInt | (intros; apply GlobalTheory.ZonalUnique.eq_mul_zonalInt <;> assumption)
end
end

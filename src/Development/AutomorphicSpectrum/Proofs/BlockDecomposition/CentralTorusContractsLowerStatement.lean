module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCentralContract

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasad

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.IwahoriInj GlobalTheory.DepthZeroJac ValuativeRel Matrix Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isEmbedding_val_GL (n : ℕ) :
    IsEmbedding (Units.val : GL (Fin n) k → Matrix (Fin n) (Fin n) k) := by
  refine Units.isEmbedding_val_mk' (f := fun A => A⁻¹) (fun A hA => ?_) fun u => by simp
  have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
  exact (continuousAt_matrix_inv _
    (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt

theorem exists_entry_nhds {n : ℕ} {V : Set (Matrix (Fin n) (Fin n) k)}
    (hV : V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ W ∈ 𝓝 (0 : k), ∀ A : Matrix (Fin n) (Fin n) k, (∀ i j, (A - 1) i j ∈ W) → A ∈ V := by
  have hS : (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) k) :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hV)
  have e : 𝓝 (0 : Matrix (Fin n) (Fin n) k) =
      Filter.pi fun _ : Fin n => Filter.pi fun _ : Fin n => 𝓝 (0 : k) := by
    show 𝓝 (0 : Fin n → Fin n → k) = _
    rw [nhds_pi]
    congr 1
    funext i
    rw [nhds_pi]
    rfl
  rw [e] at hS
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.1 hS
  have ht' : ∀ i, ∃ (I' : Finset (Fin n)) (t' : Fin n → Set k), (∀ j, t' j ∈ 𝓝 (0 : k)) ∧
      (I' : Set (Fin n)).pi t' ⊆ t i := fun i => Filter.mem_pi'.1 (ht i)
  choose I' t' h1 h2 using ht'
  refine ⟨⋂ i, ⋂ j, t' i j, Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => h1 i j,
    fun A hA => ?_⟩
  have h3 : A - 1 ∈ (fun A : Matrix (Fin n) (Fin n) k => A + 1) ⁻¹' V :=
    hsub fun i _ => h2 i fun j _ => by
      have := hA i j
      simp only [Set.mem_iInter] at this
      exact this i j
  simpa using h3

variable {s : ℕ} {d : Fin s → ℕ}

def blockScalar {c : k} (hc : c ≠ 0) (C : Fin s → ℕ) : Levi k (fun a => Fin (d a)) := fun a =>
  ⟨(c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k), (c ^ C a)⁻¹ • (1 : Matrix (Fin (d a)) (Fin (d a)) k),
    by rw [smul_mul_smul_comm, mul_inv_cancel₀ (pow_ne_zero _ hc), one_smul, one_mul],
    by rw [smul_mul_smul_comm, inv_mul_cancel₀ (pow_ne_zero _ hc), one_smul, one_mul]⟩

theorem blockScalar_central {c : k} (hc : c ≠ 0) (C : Fin s → ℕ) (m : Levi k (fun a => Fin (d a))) :
    blockScalar hc C * m = m * blockScalar hc C := by
  funext a
  refine Units.ext ?_
  show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) * (m a).val =
    (m a).val * ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k))
  simp

theorem leviEmb_blockScalar {n : ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {c : k} (hc : c ≠ 0)
    (C : Fin s → ℕ) : leviEmb k e (blockScalar hc C) = dia e hc C := by
  refine Units.ext ?_
  rw [dia_val]
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    show ((c ^ C a) • (1 : Matrix (Fin (d a)) (Fin (d a)) k)) i' j' = _
    by_cases h2 : i' = j'
    · subst h2
      simp
    · rw [Matrix.smul_apply, one_apply_ne h2, smul_zero, diagonal_apply_ne]
      simpa using h2
  · rw [leviEmb_apply_ne k e _ h, diagonal_apply_ne]
    exact fun h' => h (congrArg Sigma.fst (e.injective h'))

theorem valuation_conj_le {c x : k} (hc : c ≠ 0) (hv : valuation k c ≤ 1) (hx : valuation k x ≤ 1)
    {A B N : ℕ} (h : A + N ≤ B) : valuation k ((c ^ A)⁻¹ * x * c ^ B) ≤ valuation k c ^ N := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 : (c ^ A)⁻¹ * x * c ^ (A + N + r) = c ^ N * (x * c ^ r) := by
    rw [pow_add, pow_add]
    field_simp
  rw [e1, map_mul, map_mul, map_pow, map_pow]
  exact mul_le_of_le_one_right' (mul_le_one' hx (pow_le_one' hv r))

theorem expo_gap {s : ℕ} (N : ℕ) {a b : Fin s} (h : b < a) : expo s N a + N ≤ expo s N b := by
  have h1 : (b : ℕ) < a := h
  have h2 : (a : ℕ) < s := a.2
  simp only [expo]
  calc (N + 1) * (s - 1 - (a : ℕ)) + N ≤ (N + 1) * (s - 1 - (a : ℕ)) + (N + 1) := by omega
    _ = (N + 1) * (s - 1 - (a : ℕ) + 1) := by ring
    _ ≤ (N + 1) * (s - 1 - (b : ℕ)) := Nat.mul_le_mul_left _ (by omega)

end GlobalTheory.CompanionTheory.MoyPrasad
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLower

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasad

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem lowC_central_contract : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  intro k _ _ _ _ n s d e U hU
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k), Units.val ⁻¹' V ⊆ U := by
    rw [(isEmbedding_val_GL (k := k) n).nhds_eq_comap] at hU
    simpa using Filter.mem_comap.mp hU
  obtain ⟨W, hW, hWV⟩ := exists_entry_nhds hV
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).mp hW
  obtain ⟨c, hc0, hcγ, hc1⟩ : ∃ c : k, c ≠ 0 ∧ ValuativeRel.valuation k c < γ ∧
      ValuativeRel.valuation k c ≤ 1 := by
    obtain ⟨x, hx0, hx1⟩ := (Valuation.IsNontrivial.exists_lt_one : ∃ x : k, x ≠ 0 ∧ ValuativeRel.valuation k x < 1)
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (K := k) (γ : ValuativeRel.ValueGroupWithZero k)
    have hy0 : (0 : ValuativeRel.ValueGroupWithZero k) < ValuativeRel.valuation k y := by
      rw [hy]; exact Units.zero_lt γ
    rcases le_or_gt (ValuativeRel.valuation k y) 1 with hy1 | hy1
    · refine ⟨y * x, ?_, ?_, ?_⟩
      · exact mul_ne_zero (by rintro rfl; simp at hy0) hx0
      · rw [map_mul, ← hy]; exact mul_lt_of_lt_one_right hy0 hx1
      · rw [map_mul]; first | exact mul_le_one' hy1 hx1.le | exact mul_le_one₀ hy1 zero_le' hx1.le
    · refine ⟨x, hx0, ?_, hx1.le⟩
      rw [← hy]; exact hx1.trans hy1
  refine ⟨blockScalar hc0 (GlobalTheory.DepthZeroJac.expo s 1), blockScalar_central hc0 _, ?_⟩
  intro g hg
  simp only [lowC, Set.mem_ofPred_eq] at hg
  obtain ⟨hK, hlow⟩ := hg
  have hgint : ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.mp hK
    intro i j
    exact (h i j).2
  have h0W : (0 : k) ∈ W := mem_of_mem_nhds hW
  have hdiag : leviEmb k e (blockScalar hc0 (GlobalTheory.DepthZeroJac.expo s 1)) =
      GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1) := by
    refine Units.ext ?_
    rw [GlobalTheory.DepthZeroJac.dia_val]
    ext i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases h : a = b
    · subst h
      rw [leviEmb_apply_same]
      show ((c ^ GlobalTheory.DepthZeroJac.expo s 1 a) •
        (1 : Matrix (Fin (d a)) (Fin (d a)) k)) i' j' = _
      by_cases h2 : i' = j'
      · subst h2
        simp
      · rw [Matrix.smul_apply, Matrix.one_apply_ne h2, smul_zero, Matrix.diagonal_apply_ne]
        simpa using h2
    · rw [leviEmb_apply_ne k e _ h, Matrix.diagonal_apply_ne]
      exact fun h' => h (congrArg Sigma.fst (e.injective h'))
  rw [hdiag]
  refine hVU (hWV _ fun i j => ?_)
  have hentry : (((GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1))⁻¹ * g *
      GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e i))⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j *
          c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e j) := by
    simp [GlobalTheory.DepthZeroJac.dia, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Matrix.sub_apply, hentry]
  by_cases hij : blk e j < blk e i
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [Matrix.one_apply_ne hne, sub_zero]
    apply hγ
    exact ((valuation_conj_le hc0 hc1 (hgint i j) (GlobalTheory.CompanionTheory.MoyPrasad.expo_gap 1 hij)).trans_eq
      (pow_one _)).trans_lt hcγ
  · have h0 := hlow i j hij
    rw [Matrix.sub_apply, sub_eq_zero] at h0
    rw [h0]
    by_cases hij' : i = j
    · subst hij'
      simpa [hc0] using h0W
    · simpa [Matrix.one_apply_ne hij'] using h0W

end GlobalTheory.CompanionTheory.MoyPrasad

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLowerStatement

section

@[expose] public section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem _root_.GlobalTheory.T.central_torus_contracts_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | exact GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract <;> assumption)
end
end

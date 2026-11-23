module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Aesop.Main
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceNormalFiniteIndex

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem congruence_normal_finite_index : ∀ (I : AutInst), (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ IsOpen (I.Kg g) ∧ (∀ x ∈ I.Kset, ∀ y ∈ I.Kg g, x * y * x⁻¹ ∈ I.Kg g) ∧ ∃ s : Finset I.Gf, ∀ x ∈ I.Kset, ∃ t ∈ s, t⁻¹ * x ∈ I.Kg g := by
  intro I
  obtain ⟨-, -, -, hKc, -, hK, hg⟩ := GlobalTheory.CongTop.adelic_topology I
  refine ⟨hK, fun g hg1 => ?_⟩
  obtain ⟨hKgo, ⟨H, hH⟩, hnorm⟩ := hg g hg1
  refine ⟨⟨H, hH⟩, hKgo, hnorm, ?_⟩

  have hopen : ∀ t ∈ I.Kset, IsOpen {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := fun t _ =>
    hKgo.preimage (continuous_const_mul t⁻¹)
  have hsub : I.Kset ⊆ ⋃ t ∈ I.Kset, {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := by
    intro x hx
    refine Set.mem_biUnion hx ?_
    show x⁻¹ * x ∈ I.Kg g
    rw [inv_mul_cancel, ← hH]
    exact H.one_mem
  obtain ⟨b, -, hb, hcov⟩ := hKc.elim_finite_subcover_image hopen hsub
  refine ⟨hb.toFinset, fun x hx => ?_⟩
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcov hx)
  exact ⟨t, hb.mem_toFinset.mpr ht, hxt⟩

end GlobalTheory.CongTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCountData

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField Matrix
open scoped InnerProductSpace ComplexOrder Classical

namespace GlobalTheory.Mem.RowsBundle

section Infl

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem fibre_eq (q : Q) :
    ∃ t : I.Gf, {x | x ∈ I.Kset ∧ ρ.toFun x = q} = (fun y => t * y) ⁻¹' I.Kg g := by
  obtain ⟨t, ht, rfl⟩ := ρ.surj q
  have ht' : t⁻¹ ∈ I.Kset := (Ksub I).inv_mem ht
  refine ⟨t⁻¹, Set.ext fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine (ρ.ker _ ((Ksub I).mul_mem ht' h.1)).1 ?_
    rw [ρ.map_mul _ ht' _ h.1, ρ.map_inv ht, h.2, inv_mul_cancel]
  · have h1 : t⁻¹ * x ∈ I.Kset := h.1
    have hx : x ∈ I.Kset := ((Ksub I).mul_mem_cancel_left ht').1 h1
    have h2 := (ρ.ker _ h1).2 h
    rw [ρ.map_mul _ ht' _ hx, ρ.map_inv ht, inv_mul_eq_one] at h2
    exact ⟨hx, h2.symm⟩

theorem integral_inflate [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (F : Q → ℂ) :
    Integrable (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) μf ∧
      ∫ x, (if x ∈ I.Kset then F (ρ.toFun x) else 0) ∂μf = ((μf (I.Kg g)).toReal : ℂ) * ∑ q, F q := by
  have hU : IsOpen (I.Kg g) := I.topf_open g hg
  have hfin : μf (I.Kg g) ≠ ⊤ :=
    ((measure_mono (show I.Kg g ⊆ I.Kset from fun x hx => hx.1)).trans_lt
      (GlobalTheory.adelicStab_isCompact_isOpen I).1.measure_lt_top).ne
  have hm : ∀ q, MeasurableSet {x | x ∈ I.Kset ∧ ρ.toFun x = q} ∧
      μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) := fun q => by
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨(hU.preimage (by fun_prop)).measurableSet, measure_preimage_mul μf t _⟩
  have e : (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) =
      fun x => ∑ q, {x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q) x := by
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [if_pos hx, Finset.sum_eq_single (ρ.toFun x)]
      · rw [Set.indicator_of_mem]
        exact ⟨hx, rfl⟩
      · exact fun q _ hq => Set.indicator_of_notMem (by exact fun h => hq h.2.symm) _
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (by exact fun h => hx h.1) _).symm
  have hi : ∀ q, Integrable ({x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q)) μf := fun q =>
    (integrable_indicator_iff (hm q).1).2 (integrableOn_const ((hm q).2 ▸ hfin))
  rw [e]
  refine ⟨integrable_finsetSum _ fun q _ => hi q, ?_⟩
  rw [integral_finsetSum _ fun q _ => hi q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hm q).1, Measure.real, (hm q).2, Complex.real_smul]

theorem integrable_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q) :
    Integrable (ρ.lift μf a) μf := by
  letI := Fintype.ofFinite Q
  exact (integral_inflate ρ μf hg fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ)).1

theorem lift_biinv (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (x : I.Gf) (k : I.Gf) (hk : k ∈ I.Kg g)
    (k' : I.Gf) (hk' : k' ∈ I.Kg g) : ρ.lift μf a (k * x * k') = ρ.lift μf a x := by
  by_cases hx : x ∈ I.Kset
  · have h1 : k * x ∈ I.Kset := (Ksub I).mul_mem hk.1 hx
    rw [ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a ((Ksub I).mul_mem h1 hk'.1), ρ.map_mul _ h1 _ hk'.1,
      ρ.map_mul _ hk.1 _ hx, (ρ.ker _ hk.1).2 hk, (ρ.ker _ hk'.1).2 hk', one_mul, mul_one]
  · rw [ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a fun h => hx
      (((Ksub I).mul_mem_cancel_left hk.1).1 (((Ksub I).mul_mem_cancel_right hk'.1).1 h))]

end Infl

section Tens

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

end Tens

end GlobalTheory.Mem.RowsBundle
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.InflBasic

open GlobalTheory.RowLev.Inhab GlobalTheory.Mem.RowsBundle

theorem finite_of_red {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (hg : 1 ≤ g) : Finite Q := by
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, -, -, s, hs⟩ := hK g hg
  refine Finite.of_surjective (fun t : s => ρ.toFun t) ?_
  intro q
  obtain ⟨x, hx, rfl⟩ := ρ.surj q
  obtain ⟨t, ht, htx⟩ := hs x hx
  have hk : t⁻¹ * x ∈ I.Kset := htx.1
  have htK : t ∈ I.Kset := by
    have hmem := (Ksub I).mul_mem ((mem_Ksub I x).2 hx) ((Ksub I).inv_mem ((mem_Ksub I _).2 hk))
    rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at hmem
    exact (mem_Ksub I t).1 hmem
  refine ⟨⟨t, ht⟩, ?_⟩
  show ρ.toFun t = ρ.toFun x
  calc ρ.toFun t = ρ.toFun t * ρ.toFun (t⁻¹ * x) := by rw [(ρ.ker _ hk).2 htx, mul_one]
    _ = ρ.toFun (t * (t⁻¹ * x)) := (ρ.map_mul t htK _ hk).symm
    _ = ρ.toFun x := by rw [mul_inv_cancel_left]

theorem inflation_basic : ∀ (I : AutInst) (g : ℕ) (Q : Type) [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf) [μf.IsHaarMeasure], 1 ≤ g → Finite Q ∧ 0 < (μf (I.Kg g)).toReal ∧ ρ.toFun 1 = 1 ∧ (∀ x ∈ I.Kset, ρ.toFun x⁻¹ = (ρ.toFun x)⁻¹) ∧ (∀ q : Q, μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) ∧ IsOpen {x | x ∈ I.Kset ∧ ρ.toFun x = q}) ∧ (∀ a, Integrable (ρ.lift μf a) μf ∧ IsLocallyConstant (ρ.lift μf a) ∧ ∀ x, ∀ k ∈ I.Kg g, ∀ k' ∈ I.Kg g, ρ.lift μf a (k * x * k') = ρ.lift μf a x) ∧ (∀ a b, ρ.lift μf (a + b) = ρ.lift μf a + ρ.lift μf b) ∧ (∀ (c : ℂ) a, ρ.lift μf (c • a) = c • ρ.lift μf a) ∧ ∀ a, ρ.lift μf a 1 = a.coeff 1 / ((μf (I.Kg g)).toReal : ℂ) := by
  intro I g Q _ ρ μf _ hg
  have hQ : Finite Q := finite_of_red ρ hg
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, hopen, -, -⟩ := hK g hg
  obtain ⟨hcpt, -, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have h1K : (1 : I.Gf) ∈ I.Kset := (mem_Ksub I 1).1 (Ksub I).one_mem
  have h1 : (1 : I.Gf) ∈ I.Kg g := (ρ.ker 1 h1K).1 ρ.map_one
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hpos : 0 < (μf (I.Kg g)).toReal :=
    ENNReal.toReal_pos (hopen.measure_pos μf ⟨1, h1⟩).ne'
      ((measure_mono hsub).trans_lt hcpt.measure_lt_top).ne
  refine ⟨hQ, hpos, ρ.map_one, fun x hx => ρ.map_inv hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨measure_preimage_mul μf t _, hopen.preimage (continuous_const_mul t)⟩
  · intro a
    refine ⟨integrable_lift ρ μf hg a, ?_, fun x k hk k' hk' => lift_biinv ρ μf a x k hk k' hk'⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hnhds : (fun y => x⁻¹ * y) ⁻¹' I.Kg g ∈ nhds x :=
      (hopen.preimage (continuous_const_mul x⁻¹)).mem_nhds (by
        show x⁻¹ * x ∈ I.Kg g
        rw [inv_mul_cancel]
        exact h1)
    filter_upwards [hnhds] with y hy
    have h := lift_biinv ρ μf a x 1 h1 (x⁻¹ * y) hy
    rwa [one_mul, mul_inv_cancel_left] at h
  · intro a b
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.add_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx,
        MonoidAlgebra.coeff_add, Finsupp.add_apply, add_div]
    · rw [Pi.add_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx,
        add_zero]
  · intro c a
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.smul_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
    · rw [Pi.smul_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, smul_zero]
  · intro a
    rw [ρ.lift_of_mem μf a h1K, ρ.map_one]

end GlobalTheory.InflBasic
end
end

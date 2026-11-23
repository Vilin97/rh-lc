module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SphericalA
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryBorelPreservesMixedModelLatticeLowerBlock

section

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.MixStab

variable {L : Type} [Field L]

theorem sum_hi {M : Type} [AddCommMonoid M] (N : ℕ) (f : Fin N → M)
    (hf : ∀ i : Fin N, i.1 < N - N / 2 → f i = 0) : ∑ i, f i = ∑ k, f (hi N k) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := hi N) (f := f)]
  · symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hni => hf i ?_
    by_contra hc
    have := i.isLt
    exact hni (Finset.mem_image.2 ⟨⟨i.1 - (N - N / 2), by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [hi]; omega)⟩)
  · intro x _ y _ hxy
    have := congrArg Fin.val hxy
    simp only [hi] at this
    exact Fin.ext (by omega)

theorem embLow_hi {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (k : Fin (n' / 2)) (l : Fin (n / 2)) :
    embLow n' n z (hi n' k) (hi n l) = z k l := by
  rw [embLow, dite_eq_left ⟨by simp [hi], by simp [hi]⟩]
  congr 1 <;> ext <;> simp [hi]

theorem embLow_eq_zero {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : r.1 < n' - n' / 2 ∨ c.1 < n - n / 2) : embLow n' n z r c = 0 := by
  rw [embLow, dite_eq_right (by omega)]

theorem mul_embLow_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n) :
    (A * embLow n' n z * B) r c = ∑ l, (∑ k, A r (hi n' k) * z k l) * B (hi n l) c := by
  rw [Matrix.mul_apply, sum_hi n]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, sum_hi n']
    · simp only [embLow_hi]
    · intro i hi'
      rw [embLow_eq_zero z i _ (Or.inl hi'), mul_zero]
  · intro j hj
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro i _
    rw [embLow_eq_zero z i j (Or.inr hj), mul_zero]

theorem lowBlock_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin (n' / 2)) (c : Fin (n / 2)) :
    (lowBlock A * z * lowBlock B) r c = ∑ l, (∑ k, A (hi n' r) (hi n' k) * z k l) * B (hi n l) (hi n c) := by
  simp only [Matrix.mul_apply, lowBlock, Matrix.submatrix_apply]

theorem exists_hi {N : ℕ} (r : Fin N) (hr : N - N / 2 ≤ r.1) : ∃ k, r = hi N k :=
  ⟨⟨r.1 - (N - N / 2), by have := r.isLt; omega⟩, Fin.ext (by simp only [hi]; omega)⟩

theorem mul_embLow_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (hB : ∀ i j : Fin n, j < i → B i j = 0) (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2) :
    (A * embLow n' n z * B) r c = embLow n' n (lowBlock A * z * lowBlock B) r c := by
  by_cases hc : c.1 < n - n / 2
  · rw [embLow_eq_zero _ r c (Or.inr hc), mul_embLow_mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hB (hi n l) c (Fin.lt_def.2 (by simp only [hi]; omega)), mul_zero]
  · have hr : n' - n' / 2 ≤ r.1 := by omega
    obtain ⟨r', rfl⟩ := exists_hi r hr
    obtain ⟨c', rfl⟩ := exists_hi c (by omega)
    rw [mul_embLow_mul_apply, embLow_hi, lowBlock_mul_apply]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_mixLat_iff {n' n : ℕ} (x : Matrix (Fin n') (Fin n) L) : x ∈ mixLat L n' n ↔
    ∀ r c, (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧
      (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) := Iff.rfl

theorem borel_mid_int {σ : L →+* L} {N : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {b : GU σ N}
    (hb : IsBorelU b) (i : Fin N) (hi' : i.rev = i) : b.1.1 i i ∈ intL L := by
  have h := P.fSatake_unit_diag hb i
  rw [hi'] at h
  have h2 := congrArg Valued.v h
  rw [map_mul, hv, map_one] at h2
  rw [mem_intL]
  by_contra hc
  rw [not_le] at hc
  have : (1 : WithZero (Multiplicative ℤ)) < Valued.v (b.1.1 i i) * Valued.v (b.1.1 i i) := one_lt_mul'' hc hc
  rw [h2] at this
  exact lt_irrefl _ this

theorem row_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (hA : ∀ i j : Fin n', j < i → A i j = 0)
    (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) (r : Fin n') (hr : n' / 2 ≤ r.1) (j : Fin n) :
    (A * a) r j = A r r * a r j := by
  rw [mem_mixLat_iff] at ha
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · intro i _ hir
    rcases lt_or_gt_of_ne hir with h1 | h1
    · rw [hA r i h1, zero_mul]
    · rw [(ha i j).1 (Or.inl (by have := Fin.lt_def.1 h1; omega)), mul_zero]
  · simp

theorem borel_mul_mem {σ : L →+* L} {n' n : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ n} {h : GU σ n'}
    (hg : IsBorelU g) (hh : IsBorelU h) (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) :
    (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n := by
  have ha' := (mem_mixLat_iff a).1 ha
  rw [mem_mixLat_iff]
  intro r c
  constructor
  · intro hrc
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [row_mul_eq _ hh a ha r (by omega)]
    rcases hrc with hr | ⟨hr, hc⟩
    · rw [(ha' r j).1 (Or.inl hr), mul_zero, zero_mul]
    · by_cases hjc : j.1 ≤ c.1
      · rw [(ha' r j).1 (Or.inr ⟨hr, by omega⟩), mul_zero, zero_mul]
      · rw [hg j c (Fin.lt_def.2 (by omega)), mul_zero]
  · intro hr hc
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · rw [row_mul_eq _ hh a ha r hr]
      by_cases hz : a r c = 0
      · rw [hz, mul_zero, zero_mul]; exact zero_mem _
      · have h1 : ¬ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2) := fun e => hz ((ha' r c).1 e)
        have hrr : r.rev = r := Fin.ext (by rw [Fin.val_rev]; omega)
        have hcc : c.rev = c := Fin.ext (by rw [Fin.val_rev]; omega)
        exact mul_mem (mul_mem (borel_mid_int hv hh r hrr) ((ha' r c).2 hr hc)) (borel_mid_int hv hg c hcc)
    · intro j _ hjc
      rcases lt_or_gt_of_ne hjc with h1 | h1
      · rw [row_mul_eq _ hh a ha r hr, (ha' r j).1 (Or.inr ⟨hr, by have := Fin.lt_def.1 h1; omega⟩), mul_zero, zero_mul]
      · rw [hg j c h1, mul_zero]
    · simp

end GlobalTheory.SphTheta.MixStab

namespace GlobalTheory.SphTheta


open MixStab in
theorem borel_mixLat_lowBlock : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ a : Matrix (Fin n') (Fin n) L, a ∈ mixLat L n' n → (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ∃ a ∈ mixLat L n' n, (∀ (r : Fin n') (c : Fin n), c.1 < n - n / 2 → a r c = 0) ∧ (h.1.1 * embLow n' n z * g.1.1 : Matrix (Fin n') (Fin n) L) = a + embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1) := by
  intro L _ _ ϖ σ q hU n n' g h hg hh
  refine ⟨fun a ha => borel_mul_mem hU.2.1 hg hh a ha, fun z => ?_⟩
  have key : ∀ (r : Fin n') (c : Fin n), n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2 →
      (h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1)) r c = 0 := fun r c e => by
    rw [Matrix.sub_apply, sub_eq_zero]
    exact mul_embLow_mul_eq _ _ hg _ r c e
  refine ⟨h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1), ?_,
    fun r c hc => key r c (Or.inr hc), (sub_add_cancel _ _).symm⟩
  rw [mem_mixLat_iff]
  intro r c
  refine ⟨fun e => key r c (by omega), fun _ hc => ?_⟩
  rw [key r c (Or.inr hc)]
  exact zero_mem _

end GlobalTheory.SphTheta
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryBorelPreservesMixedModelLatticeLowerBlockStatement

section

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ a : Matrix (Fin n') (Fin n) L, a ∈ mixLat L n' n → (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ∃ a ∈ mixLat L n' n, (∀ (r : Fin n') (c : Fin n), c.1 < n - n / 2 → a r c = 0) ∧ (h.1.1 * embLow n' n z * g.1.1 : Matrix (Fin n') (Fin n) L) = a + embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1) := by
  first | exact @GlobalTheory.SphTheta.borel_mixLat_lowBlock | exact GlobalTheory.SphTheta.borel_mixLat_lowBlock | (intros; apply GlobalTheory.SphTheta.borel_mixLat_lowBlock <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelInvariantFormUpperTriangularPairAction

section

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem isBorelU_inv_mixeq {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {g : GU σ n} (hg : IsBorelU g) :
    IsBorelU g⁻¹ := by
  intro i j hij
  exact Formalism.UG.P.spherical_upper_inv (g : GL (Fin n) L) ((Formalism.UG.P.spherical_upper_iff _).1 hg) hij

theorem mixLat_form_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) → ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (v : M), ℓ (ρ (embLow n' n z) (ω (g, h) v)) = ℓ (ω (g, h) s) * ℓ (ρ (embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1)) v) := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS ℓ hℓ huniq g h hg hh
  have hU := hS.1.unr
  have hnorm : ∀ (g : GU σ n) (h : GU σ n') (x : Matrix (Fin n') (Fin n) L),
      ω (g, h) * ρ x = ρ (h.1.1 * x * ((g.1)⁻¹ : GL (Fin n) L).1) * ω (g, h) := hS.1.norm
  have c1 : ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h →
      ∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v := by
    intro g h hg hh
    refine huniq (ℓ.comp (ω (g, h))) (fun a ha v => ?_)
    have hm := (GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock L ϖ σ q hU n n' g⁻¹ h (isBorelU_inv_mixeq hg) hh).1 a ha
    show ℓ (ω (g, h) (ρ a v)) = ℓ (ω (g, h) v)
    rw [← Module.End.mul_apply, hnorm, Module.End.mul_apply]
    exact hℓ _ hm _
  refine ⟨c1 g h hg hh, fun z v => ?_⟩
  obtain ⟨a, ha, ha0, he⟩ := (GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock L ϖ σ q hU n n' g h⁻¹ hg (isBorelU_inv_mixeq hh)).2 z
  have key : ρ (embLow n' n z) * ω (g, h) = ω (g, h) * ρ ((h⁻¹).1.1 * embLow n' n z * g.1.1) := by
    rw [hnorm]
    congr 2
    simp [Matrix.mul_assoc]
  set E' := embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1) with hE'
  have h0 : locH σ δ (antiG L n) (antiG L n') a E' = 0 := by
    rw [locH_antiG]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_)
    by_cases hj : j.1 < n - n / 2
    · rw [ha0 i j hj, zero_mul]
    · rw [hE', embLow, dite_eq_right (by simp only [Fin.val_rev]; omega), map_zero, mul_zero]
  have hsplit : ρ (a + E') = ρ a * ρ E' := by
    rw [hS.1.rho_mul, h0]
    simp
  rw [← Module.End.mul_apply, key, Module.End.mul_apply, c1 g h hg hh, he, hsplit, Module.End.mul_apply, hℓ a ha]

end GlobalTheory.SphTheta
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelInvariantFormUpperTriangularPairActionStatement

section

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mixedModelInvariantForm_upperTriangular_pair_action : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) → ∀ (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ v, ℓ (ω (g, h) v) = ℓ (ω (g, h) s) * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (v : M), ℓ (ρ (embLow n' n z) (ω (g, h) v)) = ℓ (ω (g, h) s) * ℓ (ρ (embLow n' n (lowBlock (h⁻¹).1.1 * z * lowBlock g.1.1)) v) := by
  first | exact @GlobalTheory.SphTheta.mixLat_form_borel | exact GlobalTheory.SphTheta.mixLat_form_borel | (intros; apply GlobalTheory.SphTheta.mixLat_form_borel <;> assumption)
end
end

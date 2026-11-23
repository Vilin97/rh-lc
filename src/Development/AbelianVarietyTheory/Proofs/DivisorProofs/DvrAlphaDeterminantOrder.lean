module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspace
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
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiEigenSublatticeFreeEqDifferentScaledStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspaceStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.latticeDetRelation_herbrand_eigenspace : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) = q → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) (∑ s ∈ Finset.univ.erase τ, (Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ ((a τ : C) - (a s : C))) := by
  first | exact @GlobalTheory.HerbrandBridge.exForm | exact GlobalTheory.HerbrandBridge.exForm | (intros; apply GlobalTheory.HerbrandBridge.exForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShift

section

@[expose] public section

open scoped NNReal

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem addVal_inv_pow_mul {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {d c : C} (hd : d ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    addVal w ℓ (d⁻¹ ^ n * c) = addVal w ℓ c - (n : ℝ) * addVal w ℓ d := by
  have hwd : ((w d : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hd)
  have hwc : ((w c : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hc)
  have hl : Real.log ((w ℓ : ℝ≥0) : ℝ) ≠ 0 := by
    refine (Real.log_neg ?_ ?_).ne
    · exact_mod_cast h0
    · exact_mod_cast h1
  unfold addVal
  rw [map_mul, map_pow, map_inv₀]
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero hwd)) hwc, Real.log_pow, Real.log_inv]
  field_simp
  ring

theorem detRel_of_detRel_lsmul (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (p q : ℕ) (F : Submodule C (Fin (p + q) → C))
    (X0 : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring)
    (hd : d ≠ 0)
    (h : DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y) :
    DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * addVal w ℓ (d : C)) := by
  obtain ⟨x, u, m, c, hx, hu, hm, hmF, ⟨hc0, hcy⟩, hdet⟩ := h
  have hdC : (d : C) ≠ 0 := fun e => hd (Subtype.ext e)
  have hsm : ∀ v : Fin (p + q) → C, d • v = (d : C) • v := fun v => rfl
  have hinj : Function.Injective (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d) := by
    intro a b hab
    simp only [LinearMap.lsmul_apply, hsm] at hab
    exact smul_right_injective _ hdC hab
  refine ⟨fun i => (d : C)⁻¹ • x i, u, m, (d : C)⁻¹ ^ (p + q) * c, ⟨?_, ?_⟩, hu, hm, hmF,
    ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hdC)) hc0, ?_⟩, ?_⟩
  · exact hx.1.units_smul (fun _ => Units.mk0 _ (inv_ne_zero hdC))
  · apply Submodule.map_injective_of_injective hinj
    rw [← hx.2, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [hsm, smul_smul, hdC]
  · rw [addVal_inv_pow_mul w ℓ h0 h1 hdC hc0, hcy]
  · have : Matrix.of (fun i => (d : C)⁻¹ • x i) = (d : C)⁻¹ • Matrix.of x := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin, hdet, mul_assoc]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShiftStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.latticeDetRelation_of_lsmul_shift : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (p q : ℕ) (F : Submodule C (Fin (p + q) → C)) (X0 : Submodule w.valuationSubring (Fin (p + q) → C)) (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F)) (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring), d ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ (d : C)) := by
  first | exact @GlobalTheory.detRel_of_detRel_lsmul | exact GlobalTheory.detRel_of_detRel_lsmul | (intros; apply GlobalTheory.detRel_of_detRel_lsmul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanOfIsLatticeBasis

section

@[expose] public section

open scoped NNReal

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

section Core

variable {C : Type} [Field C]

theorem eq_sum_rows {n : ℕ} (U : Fin n → Fin n → C) (h : (Matrix.of U).det ≠ 0)
    (f : Fin n → C) : ∃ γ : Fin n → C, f = ∑ s, γ s • U s := by
  refine ⟨Matrix.vecMul f (Matrix.of U)⁻¹, ?_⟩
  have hu : IsUnit (Matrix.of U).det := isUnit_iff_ne_zero.mpr h
  have key : Matrix.vecMul (Matrix.vecMul f (Matrix.of U)⁻¹) (Matrix.of U) = f := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  funext j
  conv_lhs => rw [← key]
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

theorem exists_eq_sum_of_mem {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u0 : Fin p → Fin (p + q) → C) (m0 : Fin q → Fin (p + q) → C)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i)) (hm0 : ∀ k, m0 k ∈ F)
    (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) (f : Fin (p + q) → C) (hf : f ∈ F) :
    ∃ β : Fin q → C, f = ∑ k, β k • m0 k := by
  obtain ⟨γ, hγ⟩ := eq_sum_rows _ hN f
  rw [Fin.sum_univ_add] at hγ
  simp only [Fin.append_left, Fin.append_right] at hγ
  have hz : ∑ i, γ (Fin.castAdd q i) • F.mkQ (u0 i) = 0 := by
    have h1 := congrArg F.mkQ hγ
    have hf0 : F.mkQ f = 0 := by simpa using hf
    have hm : ∑ k, γ (Fin.natAdd p k) • F.mkQ (m0 k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hm0 k]

    rw [hf0, map_add (f := _), map_sum, map_sum] at h1
    simp only [map_smul] at h1
    rw [hm, add_zero] at h1
    exact h1.symm
  have h0 := Fintype.linearIndependent_iff.1 hli _ hz
  exact ⟨fun k => γ (Fin.natAdd p k), by rw [hγ]; simp [h0]⟩

theorem det_append_eq {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u u0 : Fin p → Fin (p + q) → C) (m m0 : Fin q → Fin (p + q) → C)
    (A : Matrix (Fin p) (Fin p) C) (B : Matrix (Fin q) (Fin q) C)
    (hu : ∀ i, F.mkQ (u i) = ∑ j, A i j • F.mkQ (u0 j))
    (hm : ∀ i, m i = ∑ j, B i j • m0 j)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i))
    (hm0 : ∀ k, m0 k ∈ F) (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) :
    (Matrix.of (Fin.append u m)).det = A.det * B.det * (Matrix.of (Fin.append u0 m0)).det := by
  have hmem : ∀ i, u i - ∑ j, A i j • u0 j ∈ F := by
    intro i
    have : F.mkQ (u i - ∑ j, A i j • u0 j) = 0 := by

      rw [map_sub, map_sum, hu i]; simp only [map_smul]; exact sub_self _
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  choose β hβ using fun i => exists_eq_sum_of_mem F u0 m0 hli hm0 hN _ (hmem i)
  have key : (Matrix.of (Fin.append u m)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A (Matrix.of β) 0 B *
        (Matrix.of (Fin.append u0 m0)).submatrix finSumFinEquiv finSumFinEquiv := by
    ext r c
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | k
    · have hi : u i = ∑ j, A i j • u0 j + ∑ k, β i k • m0 k := by rw [← hβ i]; abel
      simp [Matrix.fromBlocks, hi, Finset.sum_apply]
    · simp [Matrix.fromBlocks, hm k, Finset.sum_apply]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_submatrix_equiv_self]

theorem comp_sum {W : Type} [AddCommGroup W] [Module C W] {n k l : ℕ} (a : Fin n → W)
    (b : Fin k → W) (c : Fin l → W) (P : Matrix (Fin k) (Fin n) C)
    (Q : Matrix (Fin l) (Fin k) C) (hb : ∀ i, b i = ∑ j, P i j • a j)
    (hc : ∀ i, c i = ∑ j, Q i j • b j) : ∀ i, c i = ∑ j, (Q * P) i j • a j := by
  intro i
  simp only [hc i, hb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

end Core

section Lattice

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem coeffs {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n k : ℕ} (a : Fin n → W) (b : Fin k → W)
    (h : ∀ i, b i ∈ Submodule.span w.valuationSubring (Set.range a)) :
    ∃ P : Matrix (Fin k) (Fin n) w.valuationSubring,
      ∀ i, b i = ∑ j, algebraMap w.valuationSubring C (P i j) • a j := by
  choose P hP using fun i =>
    (Submodule.mem_span_range_iff_exists_fun w.valuationSubring).1 (h i)
  exact ⟨Matrix.of P, fun i => by
    rw [← hP i]; exact Finset.sum_congr rfl fun j _ => (algebraMap_smul C (P i j) (a j)).symm⟩

theorem mem_span_of_isLatticeBasis {W : Type} [AddCommGroup W] [Module C W]
    [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] {n k : ℕ}
    {a : Fin n → W} {b : Fin k → W} {Y : Submodule w.valuationSubring W}
    (ha : IsLatticeBasis w a Y) (hb : IsLatticeBasis w b Y) (i : Fin k) :
    b i ∈ Submodule.span w.valuationSubring (Set.range a) := by
  rw [ha.2, ← hb.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem transition {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (a b : Fin n → W)
    (Y : Submodule w.valuationSubring W) (ha : IsLatticeBasis w a Y)
    (hb : IsLatticeBasis w b Y) :
    ∃ P : Matrix (Fin n) (Fin n) C, (∀ i, b i = ∑ j, P i j • a j) ∧ w P.det = 1 := by
  obtain ⟨P, hP⟩ := coeffs a b (mem_span_of_isLatticeBasis ha hb)
  obtain ⟨Q, hQ⟩ := coeffs b a (mem_span_of_isLatticeBasis hb ha)
  have hQP := comp_sum a b a (P.map (algebraMap w.valuationSubring C))
    (Q.map (algebraMap w.valuationSubring C)) hP hQ
  have hone : (Q.map (algebraMap w.valuationSubring C)) * (P.map (algebraMap w.valuationSubring C))
      = 1 := by
    ext i j
    have h := Fintype.linearIndependent_iff.1 ha.1
      (fun j => ((Q.map (algebraMap w.valuationSubring C)) *
        (P.map (algebraMap w.valuationSubring C))) i j - (1 : Matrix (Fin n) (Fin n) C) i j)
      (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hQP i]
        simp [Matrix.one_apply])
      j
    exact sub_eq_zero.1 h
  have hdet := congrArg Matrix.det hone
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hle : ∀ R : Matrix (Fin n) (Fin n) w.valuationSubring,
      w (R.map (algebraMap w.valuationSubring C)).det ≤ 1 := by
    intro R
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ValuationSubring.algebraMap_apply]
    exact (w.mem_valuationSubring_iff _).1 R.det.2
  refine ⟨P.map (algebraMap w.valuationSubring C), fun i => hP i, le_antisymm (hle P) ?_⟩
  calc (1 : ℝ≥0) = w (Q.map (algebraMap w.valuationSubring C)).det *
        w (P.map (algebraMap w.valuationSubring C)).det := by rw [← map_mul, hdet, map_one]
    _ ≤ w (P.map (algebraMap w.valuationSubring C)).det :=
        mul_le_of_le_one_left (by positivity) (hle Q)

end Lattice

end GlobalTheory.DetRelCompare

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

end GlobalTheory.DetRelCompare
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantOrder

section

@[expose] public section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.FrameModel

theorem det_append_eq_mul_det : ∀ (C : Type) [Field C] (w : Valuation C NNReal) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → ∀ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C) (m : Fin q → Fin (p + q) → C), GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w x (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w (fun i => (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ).mkQ (u i)) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w m (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) → ∃ c : C, w c = ∏ s ∈ Finset.univ.erase τ, w ((a τ : C) - (a s : C)) ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) ∧ (Matrix.of (Fin.append u m)).det = c * (Matrix.of x).det := by
  intro C _ w ℓ hℓ0 hℓ1 S _ _ a p q Fil τ ha hFil x u m hx hu hm
  set F := GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ with hF
  have hfin : Module.finrank C F = q := by
    have hsp : F = Submodule.span C (Set.range m) := by
      rw [hF, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace, ← hm.2, Submodule.span_span_of_tower]
    rw [hsp, finrank_span_eq_card hm.1, Fintype.card_fin]
  have hd0 : GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr ?_
    exact ha.ne (Finset.ne_of_mem_erase hs).symm
  have h1 := GlobalTheory.T.latticeDetRelation_herbrand_eigenspace C w ℓ hℓ0 hℓ1 S a p q Fil τ ha hFil hfin
  rw [GlobalTheory.T.piEigenSublattice_free_eq_differentScaled C w S a (p + q) τ ha] at h1
  have h2 := GlobalTheory.T.latticeDetRelation_of_lsmul_shift C w ℓ hℓ0 hℓ1 p q _ _ _ _ _ _ hd0 h1
  obtain ⟨x', u', m', c, hx', hu', hm', hmF, ⟨hc0, hcv⟩, hdet⟩ := h2
  obtain ⟨P, hP, hPdet⟩ := GlobalTheory.DetRelCompare.transition x' x _ hx' hx
  obtain ⟨A, hA, hAdet⟩ := GlobalTheory.DetRelCompare.transition _ _ _ hu' hu
  obtain ⟨B, hB, hBdet⟩ := GlobalTheory.DetRelCompare.transition m' m _ hm' hm
  have hx'0 : (Matrix.of x').det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp hx'.1)).ne_zero
  have happ0 : (Matrix.of (Fin.append u' m')).det ≠ 0 := by
    intro h0
    exact hx'0 (by rw [hdet, h0, mul_zero])
  have hrel := GlobalTheory.DetRelCompare.det_append_eq F u u' m m' A B hA hB hu'.1 hmF happ0
  have hxP : (Matrix.of x).det = P.det * (Matrix.of x').det := by
    have hmat : Matrix.of x = P * Matrix.of x' := by
      ext i k
      simp [Matrix.mul_apply, hP i, Finset.sum_apply]
    rw [hmat, Matrix.det_mul]
  have hP0 : P.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hPdet
    exact zero_ne_one hPdet
  refine ⟨A.det * B.det * (P.det * c)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv₀, map_mul, hAdet, hBdet, hPdet, one_mul, one_mul, one_mul]
    have hlam : Real.log (w ℓ : ℝ) ≠ 0 :=
      (Real.log_neg (NNReal.coe_pos.mpr hℓ0) (NNReal.coe_lt_one.mpr hℓ1)).ne
    have hds : ∀ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ) ≠ 0 := by
      intro s hs
      rw [NNReal.coe_ne_zero, Valuation.ne_zero_iff]
      exact sub_ne_zero.mpr (Subtype.coe_injective.ne (ha.ne (Finset.ne_of_mem_erase hs).symm))
    have hdiff : ((GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ : w.valuationSubring) : C)
        = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen]
    have hle : ∀ s, Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) ≤ p + q := fun s =>
      (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun C)
    have hlogc : Real.log (w c : ℝ) = - ∑ s ∈ Finset.univ.erase τ,
        ((p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℕ) : ℝ)
          * Real.log (w ((a τ : C) - (a s : C)) : ℝ) := by
      have e := hcv
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal] at e
      rw [hdiff, map_prod, NNReal.coe_prod, Real.log_prod hds, div_eq_iff hlam] at e
      rw [e, sub_mul, Finset.sum_mul, mul_assoc, div_mul_cancel₀ _ hlam, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Nat.cast_sub (hle s)]
      field_simp
      ring
    have hwc : 0 < ((w c : NNReal) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff w).mpr hc0))
    apply NNReal.coe_injective
    rw [NNReal.coe_inv, NNReal.coe_prod]
    simp only [NNReal.coe_pow]
    have hpos2 : 0 < ∏ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ)
        ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) :=
      Finset.prod_pos fun s hs => pow_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (hds s hs).symm) _
    rw [← Real.exp_log (inv_pos.mpr hwc), ← Real.exp_log hpos2, Real.log_inv, hlogc, neg_neg,
      Real.log_prod fun s hs => pow_ne_zero _ (hds s hs)]
    simp only [Real.log_pow]
  · rw [hrel, hxP, hdet]
    field_simp

end GlobalTheory.FrameModel

namespace GlobalTheory.FrameModel

section Small

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

end Small

end GlobalTheory.FrameModel
end
end

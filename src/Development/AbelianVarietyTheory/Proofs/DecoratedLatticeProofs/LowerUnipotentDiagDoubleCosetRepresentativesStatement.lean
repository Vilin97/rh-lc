module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLowerUnipotentBlockDiagCosetRep

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke GlobalTheory.ParHeckeSource GlobalTheory.ParahoricConjBlocks

noncomputable section

namespace GlobalTheory.LowerHecke

theorem lowU_conj_blocks {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (M W : Matrix D D k) (ν : Matrix D A k) (a : Matrix A A k) (b : Matrix A D k) (c : Matrix D A k) (e : Matrix D D k) :
    fromBlocks 1 0 0 M * fromBlocks 1 0 (-ν) 1 * fromBlocks a b c e * fromBlocks 1 0 0 W =
      fromBlocks a (b * W) (M * (c - ν * a)) (M * (e - ν * b) * W) := by
  simp only [fromBlocks_multiply]
  congr 1 <;> simp [Matrix.mul_sub, sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] <;> abel

end GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

theorem exists_lowU_diag_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ j ∈ parahoric k A D, ∃ g ∈ R, ∃ ν₀ : Matrix D A k, (∀ i a, valuation k (ν₀ i a) < 1) ∧ ∀ ν : Matrix D A k, (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν₀ - ν = g.1 * μ) → (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) ∈ parahoric k A D := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ j hj
  set w := torusElt k D ϖ (indic s) with hw
  have hjI : IsIntM j.1 := isIntM_of_mem_parahoric hj
  have hjl : ∀ i l, valuation k (j.1 (.inr i) (.inl l)) < 1 := (mem_parahoric.1 hj).2
  have hjd : valuation k j.1.det = 1 := val_det_of_mem_KO (mem_parahoric.1 hj).1
  obtain ⟨ha, he⟩ := (val_det_iff_of_lower j.1 (fun i l => hjI i l) hjl).1 hjd
  obtain ⟨haI, hbI, hcI, heI⟩ := isIntM_toBlocks hjI
  set a := j.1.toBlocks₁₁ with ha_def
  set b := j.1.toBlocks₁₂ with hb_def
  set c := j.1.toBlocks₂₁ with hc_def
  set e := j.1.toBlocks₂₂ with he_def
  have hcM : ∀ i l, valuation k (c i l) < 1 := fun i l => hjl i l
  have ha0 : IsUnit a.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at ha; exact zero_ne_one ha
  have hainvI : IsIntM a⁻¹ := isIntM_inv haI ha
  have hinva : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha0
  letI : Invertible a := Matrix.invertibleOfIsUnitDet a ha0
  set E := e - c * a⁻¹ * b with hE_def
  have hjE : j.1.det = a.det * E.det := by
    rw [← fromBlocks_toBlocks j.1, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hEd : valuation k E.det = 1 := by
    rw [hjE, map_mul, ha, one_mul] at hjd; exact hjd
  have hEI : IsIntM E := isIntM_sub heI (isIntM_mul (isIntM_mul hcI hainvI) hbI)
  have hEu : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).2
    (isUnit_iff_ne_zero.2 fun h0 => by rw [h0, map_zero] at hEd; exact zero_ne_one hEd)
  set E' : GL D k := hEu.unit with hE'_def
  have hE'v : E'.1 = E := hEu.unit_spec
  have hE'K : E' ∈ KO k D := mem_KO_of (by rw [hE'v]; exact hEI) (by rw [hE'v]; exact hEd)
  obtain ⟨g, ⟨hgR, hgK⟩, -⟩ := hR.2 E' hE'K
  obtain ⟨hκg, hκ'g, hgeq⟩ := hκ g hgR

  refine ⟨g, hgR, c * a⁻¹, fun i l => GlobalTheory.StepData.MaxM.mul_intM (k := k) hcM (fun i l => hainvI i l) i l, ?_⟩
  rintro ν ⟨μ, hμ, hνμ⟩
  have hν : ν = c * a⁻¹ - g.1 * μ := by rw [← hνμ]; abel
  set K1 := κ g with hK1
  set K2 := κ' g with hK2
  have hm : (w⁻¹ * K1⁻¹) * g = K2 := by rw [hgeq]; group
  have hm' : K2 * g⁻¹ = w⁻¹ * K1⁻¹ := by rw [← hm]; group
  have hX : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, K1) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) =
      emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w) := by
    rw [mtor_eq, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_lowU, ← map_inv, ← map_inv, Prod.inv_mk, Prod.inv_mk,
      inv_one, ← emb_mul_emb]
    simp only [mul_assoc, hw]
  rw [hX]
  set M : Matrix D D k := (w⁻¹ * K1⁻¹).1 with hM
  have hXv : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1 =
      fromBlocks a (b * w.1) (M * (c - ν * a)) (M * (e - ν * b) * w.1) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_emb_one, val_emb_one, val_lowU, ← fromBlocks_toBlocks j.1]
    exact lowU_conj_blocks _ _ _ _ _ _ _
  have h21 : M * (c - ν * a) = K2.1 * (μ * a) := by
    rw [hν, Matrix.sub_mul, Matrix.mul_assoc c, hinva, Matrix.mul_one, sub_sub_cancel, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hM, ← Units.val_mul, hm, Matrix.mul_assoc]
  have he' : e - ν * b = E + g.1 * μ * b := by rw [hν, hE_def, Matrix.sub_mul]; abel
  have h22 : M * (e - ν * b) * w.1 = (K2 * (g⁻¹ * (E' * w))).1 + K2.1 * (μ * b * w.1) := by
    rw [he', Matrix.mul_add, Matrix.add_mul]
    congr 1
    · rw [hM, ← hm', ← hE'v]; simp only [Units.val_mul, Matrix.mul_assoc]
    · rw [← hm, hM]; simp only [Units.val_mul, Matrix.mul_assoc]
  have hwI : IsIntM w.1 := by
    have h := inv_torusElt_int (D := D) hϖ s
    rw [val_inv_torusElt] at h
    rw [hw, val_torusElt]; simpa using h
  have hμa : ∀ i l, valuation k ((μ * a) i l) < 1 := GlobalTheory.StepData.MaxM.mul_intM (k := k) hμ (fun i l => haI i l)
  have hll : ∀ i l, valuation k ((K2.1 * (μ * a)) i l) < 1 := val_lt_mul (isIntM_of_mem_KO hκ'g) hμa
  have hwdet : (w⁻¹).1.det * w.1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine mem_parahoric_of ?_ ?_ ?_
  · rw [hXv, h21, h22]
    refine isIntM_fromBlocks_iff.2 ⟨haI, isIntM_mul hbI hwI, fun i l => (hll i l).le, ?_⟩
    intro i l
    exact add_mem (isIntM_of_mem_KO (mul_mem hκ'g hgK) i l)
      (isIntM_mul (isIntM_of_mem_KO hκ'g) (isIntM_mul (isIntM_mul (fun i l => (hμ i l).le) hbI) hwI) i l)
  · have hdet : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1.det =
        (K1⁻¹).1.det * j.1.det * ((w⁻¹).1.det * w.1.det) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, val_emb_one,
        val_emb_one, val_lowU, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, Units.val_mul,
        Matrix.det_mul]
      simp only [Matrix.det_one]; ring
    rw [hdet, hwdet, mul_one, map_mul, hjd, mul_one]
    exact val_det_of_mem_KO (inv_mem hκg)
  · intro i l
    rw [hXv, fromBlocks_apply₂₁, h21]
    exact hll i l

end GlobalTheory.LowerHecke

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLowerUnipotentBlockDiagCosetRepStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

theorem _root_.GlobalTheory.T.exists_lowerUnipotent_blockDiag_coset_rep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ j ∈ parahoric k A D, ∃ g ∈ R, ∃ ν₀ : Matrix D A k, (∀ i a, valuation k (ν₀ i a) < 1) ∧ ∀ ν : Matrix D A k, (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν₀ - ν = g.1 * μ) → (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) ∈ parahoric k A D := by
  first | exact @GlobalTheory.LowerHecke.exists_lowU_diag_coset | exact GlobalTheory.LowerHecke.exists_lowU_diag_coset | (intros; apply GlobalTheory.LowerHecke.exists_lowU_diag_coset <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentBlockDiagCosetsDistinct

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

noncomputable section

namespace GlobalTheory.CosetDistinct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

local notation "E" m:arg => emb₂ k (Equiv.refl (A ⊕ D)) (1, m)

theorem lowU_mul_lowU (a b : Matrix D A k) : (lowU a * lowU b : GL (A ⊕ D) k) = lowU (a + b) := by
  ext1; rw [Units.val_mul, val_lowU, val_lowU, val_lowU, fromBlocks_multiply]; simp [add_comm]

theorem emb_one_inv (m : GL D k) : (E m)⁻¹ = E (m⁻¹) := by rw [← map_inv]; simp

theorem quot_eq (ν ν' : Matrix D A k) (a b w : GL D k) :
    (lowU ν * (E a) * (E w))⁻¹ * (lowU ν' * (E b) * (E w)) =
      lowU (((a * w)⁻¹ : GL D k).1 * (ν' - ν)) * (E ((a * w)⁻¹ * (b * w))) := by
  have h : lowU ν' = (lowU ν * lowU (ν' - ν) : GL (A ⊕ D) k) := by rw [lowU_mul_lowU]; congr 1; abel
  rw [h, ← emb_mul_emb (a * w)⁻¹ (b * w), ← emb_mul_emb b w,
    ← mul_assoc (lowU (((a * w)⁻¹ : GL D k).1 * (ν' - ν))), ← emb_mul_lowU, ← emb_one_inv,
    ← emb_mul_emb a w]
  group

theorem lowU_emb_apply_inr_inl (X : Matrix D A k) (Y : GL D k) (i : D) (j : A) :
    (lowU X * (E Y) : GL (A ⊕ D) k).1 (.inr i) (.inl j) = X i j := by
  rw [Units.val_mul, val_lowU, val_emb_one, fromBlocks_multiply]; simp

theorem mem_KO_of_emb {Y : GL D k} (h : (E Y) ∈ KO k (A ⊕ D)) : Y ∈ KO k D := by
  rw [GlobalTheory.StepData.mem_KO] at h ⊢
  refine ⟨fun i j => by simpa [val_emb_one] using h.1 (.inr i) (.inr j), fun i j => ?_⟩
  have := h.2 (.inr i) (.inr j)
  rw [emb_one_inv, val_emb_one] at this; simpa using this

theorem inv_mul_of_eq {G : Type*} [Group G] {x a w b : G} (h : x = a * w * b) (c : G) :
    x⁻¹ * c = b⁻¹ * ((a * w)⁻¹ * c) := by subst h; group

theorem mul_inv_of_eq {G : Type*} [Group G] {x a w b : G} (h : x = a * w * b) : x * b⁻¹ = a * w := by
  subst h; group

theorem coset_uniq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ g ∈ R, ∀ g' ∈ R, ∀ ν ν' : Matrix D A k, (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (lowU ν' * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g') * mtor ϖ (indic s)) ∈ parahoric k A D → g = g' ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν' - ν = g.1 * μ := by
  intro k _ _ _ _ A D _ _ _ _ ϖ _ s R hR κ κ' hκ g hg g' hg' ν ν' hmem
  rw [mtor_eq (A := A), quot_eq] at hmem
  obtain ⟨hk1, hk1', hgeq⟩ := hκ g hg
  obtain ⟨hk2, hk2', hg'eq⟩ := hκ g' hg'
  have hXm : ∀ i a, valuation k (((((κ g * torusElt k D ϖ (indic s))⁻¹ : GL D k).1 * (ν' - ν))) i a) < 1 :=
    fun i a => by
      have := (mem_parahoric.1 hmem).2 i a
      rwa [lowU_emb_apply_inr_inl] at this
  have hYK : (κ g * torusElt k D ϖ (indic s))⁻¹ * (κ g' * torusElt k D ϖ (indic s)) ∈ KO k D := by
    apply mem_KO_of_emb (A := A)
    have hJ := (parahoric k A D).mul_mem ((parahoric k A D).inv_mem (lowU_mem hXm)) hmem
    rw [inv_mul_cancel_left] at hJ
    exact (mem_parahoric.1 hJ).1
  have hgg : g = g' := by
    obtain ⟨g0, _, huniq⟩ := hR.2 (κ g') hk2
    have h1 : g⁻¹ * (κ g' * torusElt k D ϖ (indic s)) ∈ KO k D := by
      rw [inv_mul_of_eq hgeq]; exact mul_mem (inv_mem hk1') hYK
    have h2 : g'⁻¹ * (κ g' * torusElt k D ϖ (indic s)) ∈ KO k D := by
      rw [inv_mul_of_eq hg'eq, inv_mul_cancel, mul_one]; exact inv_mem hk2'
    exact (huniq g ⟨hg, h1⟩).trans (huniq g' ⟨hg', h2⟩).symm
  refine ⟨hgg, ((κ' g)⁻¹ : GL D k).1 * (((κ g * torusElt k D ϖ (indic s))⁻¹ : GL D k).1 * (ν' - ν)), ?_, ?_⟩
  · exact GlobalTheory.StepData.IntM.mul_maxM (GlobalTheory.StepData.intM_of_mem_KO (inv_mem hk1')) hXm
  · rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_of_eq hgeq, ← Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]

end GlobalTheory.CosetDistinct

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentBlockDiagCosetsDistinctStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

theorem _root_.GlobalTheory.T.lowerUnipotent_blockDiag_cosets_distinct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ g ∈ R, ∀ g' ∈ R, ∀ ν ν' : Matrix D A k, (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (lowU ν' * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g') * mtor ϖ (indic s)) ∈ parahoric k A D → g = g' ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν' - ν = g.1 * μ := by
  first | exact @GlobalTheory.CosetDistinct.coset_uniq | exact GlobalTheory.CosetDistinct.coset_uniq | (intros; apply GlobalTheory.CosetDistinct.coset_uniq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentDiagDoubleCosetRepresentatives

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

theorem repsBuild : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ N : GL D k → Finset (Matrix D A k), (∀ g ∈ R, (∀ ν ∈ N g, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N g ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → ∃ R' : Finset (GL (A ⊕ D) k), IsReps (mtor ϖ (indic s)) R' blockDet ∧ ∀ F : GL (A ⊕ D) k → ℂ, ∑ j ∈ R', F j = ∑ g ∈ R, ∑ ν ∈ N g, F (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ N hN
  classical
  set t : GL (A ⊕ D) k := mtor ϖ (indic s) with ht
  let f : (Σ _ : GL D k, Matrix D A k) → GL (A ⊕ D) k :=
    fun x => lowU x.2 * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ x.1)

  have key : ∀ g₁ ∈ R, ∀ ν₁ ∈ N g₁, ∀ g₂ ∈ R, ∀ ν₂ ∈ N g₂,
      (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D → g₁ = g₂ ∧ ν₁ = ν₂ := by
    intro g₁ hg₁ ν₁ hν₁ g₂ hg₂ ν₂ hν₂ h
    obtain ⟨rfl, μ, hμ, hdiff⟩ := GlobalTheory.T.lowerUnipotent_blockDiag_cosets_distinct k A D ϖ hϖ s R hR κ κ' hκ g₁ hg₁ g₂ hg₂ ν₁ ν₂ h
    refine ⟨rfl, ?_⟩
    obtain ⟨hsmall, huniq⟩ := hN g₁ hg₁
    obtain ⟨ν', _, hν'⟩ := huniq ν₂ (hsmall ν₂ hν₂)
    have e2 : ν₂ = ν' := hν' ν₂ ⟨hν₂, 0, fun i a => by simp, by simp⟩
    have e1 : ν₁ = ν' := hν' ν₁ ⟨hν₁, μ, hμ, hdiff⟩
    rw [e1, e2]
  refine ⟨(R.sigma N).image f, ⟨?_, ?_⟩, ?_⟩
  · intro j hj
    obtain ⟨⟨g, ν⟩, hx, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_sigma] at hx
    obtain ⟨hg, hν⟩ := hx
    refine ⟨Subgroup.mul_mem _ (lowU_mem ((hN g hg).1 ν hν)) (emb_mem (hκ g hg).1), ?_⟩
    have h22 : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)).1.toBlocks₂₂ = (κ g).1 := by
      rw [Units.val_mul, val_emb_one, val_lowU, fromBlocks_multiply]; simp
    show ((blockDet (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) : kˣ) : k) = _
    rw [blockDet_lowU_emb, h22, GeneralLinearGroup.val_det_apply]
  · intro j hj
    obtain ⟨g, hg, ν₀, hν₀, hall⟩ := GlobalTheory.T.exists_lowerUnipotent_blockDiag_coset_rep k A D ϖ hϖ s R hR κ κ' hκ j hj
    obtain ⟨ν', ⟨hν'N, μ, hμ, hdiff⟩, -⟩ := (hN g hg).2 ν₀ hν₀
    refine ⟨f ⟨g, ν'⟩, ⟨Finset.mem_image.2 ⟨(⟨g, ν'⟩ : Σ _ : GL D k, Matrix D A k), Finset.mem_sigma.2 ⟨hg, hν'N⟩, rfl⟩,
      hall ν' ⟨μ, hμ, hdiff⟩⟩, ?_⟩
    rintro j' ⟨hj', hmem⟩
    obtain ⟨⟨g₂, ν₂⟩, hx, rfl⟩ := Finset.mem_image.1 hj'
    rw [Finset.mem_sigma] at hx
    have hmem' : (f ⟨g, ν'⟩ * t)⁻¹ * (j * t) ∈ parahoric k A D := hall ν' ⟨μ, hμ, hdiff⟩
    have hc : (f ⟨g₂, ν₂⟩ * t)⁻¹ * (f ⟨g, ν'⟩ * t) ∈ parahoric k A D := by
      have := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hmem')
      simpa [mul_assoc] using this
    obtain ⟨rfl, rfl⟩ := key g₂ hx.1 ν₂ hx.2 g hg ν' hν'N hc
    rfl
  · intro F
    rw [Finset.sum_image, Finset.sum_sigma]
    rintro ⟨g₁, ν₁⟩ h₁ ⟨g₂, ν₂⟩ h₂ heq
    rw [Finset.coe_sigma, Set.mem_sigma_iff] at h₁ h₂
    have hc : (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D := by
      rw [show f ⟨g₁, ν₁⟩ = f ⟨g₂, ν₂⟩ from heq, inv_mul_cancel]; exact Subgroup.one_mem _
    obtain ⟨rfl, rfl⟩ := key g₁ h₁.1 ν₁ h₁.2 g₂ h₂.1 ν₂ h₂.2 hc
    rfl

end GlobalTheory.LowerHecke
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentDiagDoubleCosetRepresentativesStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

theorem _root_.GlobalTheory.T.lowerUnipotent_diag_doubleCoset_representatives : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ N : GL D k → Finset (Matrix D A k), (∀ g ∈ R, (∀ ν ∈ N g, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N g ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → ∃ R' : Finset (GL (A ⊕ D) k), IsReps (mtor ϖ (indic s)) R' blockDet ∧ ∀ F : GL (A ⊕ D) k → ℂ, ∑ j ∈ R', F j = ∑ g ∈ R, ∑ ν ∈ N g, F (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) := by
  first | exact @GlobalTheory.LowerHecke.repsBuild | exact GlobalTheory.LowerHecke.repsBuild | (intros; apply GlobalTheory.LowerHecke.repsBuild <;> assumption)
end
end

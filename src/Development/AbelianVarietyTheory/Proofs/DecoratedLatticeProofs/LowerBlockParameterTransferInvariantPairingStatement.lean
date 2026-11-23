module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetReps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenValAddSegL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeIdentityIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoric
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepChainStepMatrixCoefficientTwisted
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumEqGenVal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumRepsDatumEq

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InSuppMulLeft

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.DatumEigenLeft

open GlobalTheory.DatumEigen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']


omit [Fintype D] [DecidableEq D] in
theorem inSupp_mul_left {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D') k}
    (hj : j ∈ parahoric k A D') : InSupp (j.val * x) ∧
      valuation k ((j.val * x).toBlocks₁₁.det - j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  obtain ⟨hxi, hxd, hxl⟩ := hx
  have hprod : ∀ i l, (j.val * x) i l ∈ 𝒪[k] := fun i l => by
    rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hJ i m) (hxi m l)
  have hcong : valuation k ((j.val * x).toBlocks₁₁.det - j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hJ _ _) (hxi _ _)
    · simp only [toBlocks₁₁, of_apply, Matrix.mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => val_mul_lt (hJ _ _) (hxl _ _)
  have hd1 : valuation k (j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hxd, mul_one, (val_det_blocks hj).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact val_mul_lt (hxi _ _) (hl _ _)
    · exact val_mul_lt (hJ _ _) (hxl _ _)

end GlobalTheory.DatumEigenLeft

namespace GlobalTheory.DatumEigenLeft
open GlobalTheory.DatumEigen

theorem omTwo_datum_inv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → ∀ j ∈ parahoric k A D', ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D') (A ⊕ D') k).toBlocks₂₂.det → omTwo μS μT (1 : GL (A ⊕ D) k) j (datum ξ⁻¹ : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) = (ξ d : ℂ) • (datum ξ⁻¹ : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ξ μS μT hξ hμ j hj d hd
  funext x
  have hK := (mem_parahoric.1 hj).1
  have hdetv : valuation k (GeneralLinearGroup.det j : k) = 1 := (nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hK)
  have hμj : μS (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hμ _ hdetv
    rwa [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
  simp only [omTwo, om, Pi.smul_apply, smul_eq_mul, nabs_det_of_mem_KO hK, MonoidHom.mul_apply, MonoidHom.inv_apply,
    map_one, inv_one, Units.val_one, one_mul, Real.one_rpow, Complex.ofReal_one, mul_one, inv_inv]
  rw [show nabs k 1 = 1 by simp [nabs], Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.mul_one, Units.val_mul,
    hμj]
  have hT : (μT (GeneralLinearGroup.det j) : ℂ) ≠ 0 := Units.ne_zero _
  have e1 : ((ξ (GeneralLinearGroup.det j) : ℂ) * (((μT (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ)) *
      ((μT (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x)) =
      (ξ (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x) := by
    rw [Units.val_inv_eq_inv_val]; field_simp
  rw [e1]
  have hx : x = j.val * ((j⁻¹ : GL (A ⊕ D') k).val * x) := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  generalize (j⁻¹ : GL (A ⊕ D') k).val * x = y at hx ⊢
  subst hx
  unfold datum
  obtain ⟨h11, h22⟩ := val_det_blocks hj
  by_cases hy : InSupp y
  · obtain ⟨hs, hc⟩ := inSupp_mul_left hy hj
    have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
    set u : kˣ := Units.mk0 _ n11 with hu
    have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
    have t1 : ξ (GeneralLinearGroup.det j) = ξ (u * d) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
      rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
      exact det_cong hj
    have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (u * Units.mk0 _ hy.det_ne) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hu, Units.val_mk0, Units.val_mk0, hy.2.1, h11, mul_one]) ?_
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hc
    rw [dite_eq_left hs, dite_eq_left hy, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv, inv_inv, t1, t2, map_mul, map_mul]
    simp only [Units.val_mul]
    ring
  · have hs : ¬ InSupp (j.val * y) := fun hs => by
      have := (inSupp_mul_left hs (inv_mem hj)).1
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
      exact hy this
    rw [dite_eq_right hs, dite_eq_right hy, mul_zero, mul_zero]

end GlobalTheory.DatumEigenLeft
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmTwoTorusLeft

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.TorusLeft

theorem sum_indic {D' : Type} [Fintype D'] [DecidableEq D'] (s : Finset D') : ∑ i, indic s i = (s.card : ℤ) := by
  simp [indic]

theorem zpow_rpow_half (q : ℝ) (hq : 0 ≤ q) (n m : ℕ) :
    ((q ^ (-(n : ℤ)) : ℝ) ^ (-(m : ℝ) / 2)) = (Real.sqrt q) ^ (n * m) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq, ← Real.rpow_intCast, ← Real.rpow_mul hq]
  congr 1
  push_cast; ring

theorem omTwo_torusLeft : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ μS μT : kˣ →* ℂˣ), IsUnram (μS * ξ⁻¹) → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ (u : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) (y : Matrix (A ⊕ D') (A ⊕ D) k), omTwo μS μT (1 : GL (A ⊕ D) k) (j * mtor ϖ (indic s)) u y = (μS ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) * (ξ (GeneralLinearGroup.det j) : ℂ) * u (((j * mtor ϖ (indic s))⁻¹ : GL (A ⊕ D') k).1 * y) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ μS μT hu s j hj u y
  have hKO : j ∈ KO k (A ⊕ D') := (mem_parahoric.1 hj).1
  have hnj : nabs k (GeneralLinearGroup.det j) = 1 := nabs_det_of_mem_KO hKO
  have hvj : valuation k ((GeneralLinearGroup.det j : kˣ) : k) = 1 := (nabs_eq_one_iff _).1 hnj
  have hξ : μS (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hu _ hvj
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
    exact this
  have hdm : GeneralLinearGroup.det (mtor ϖ (indic s) : GL (A ⊕ D') k) = ϖ ^ (s.card : ℤ) := by
    rw [GlobalTheory.ChainStepCoef.det_mtor, sum_indic]
  have hnm : nabs k (GeneralLinearGroup.det (mtor ϖ (indic s) : GL (A ⊕ D') k)) = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [GlobalTheory.ChainStepCoef.nabs_det_mtor hϖ, sum_indic]
  have hnh : nabs k (GeneralLinearGroup.det (j * mtor ϖ (indic s))) = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [map_mul, nabs_mul, hnj, hnm, one_mul]
  have hμh : μS (GeneralLinearGroup.det (j * mtor ϖ (indic s))) = ξ (GeneralLinearGroup.det j) * μS ϖ ^ s.card := by
    rw [map_mul, map_mul, hξ, hdm, zpow_natCast, map_pow]
  have hq : ((nabs k (GeneralLinearGroup.det (j * mtor ϖ (indic s))) ^ (-(Fintype.card (A ⊕ D) : ℝ) / 2) : ℝ) : ℂ)
      = ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) := by
    rw [hnh, ← Fintype.card_sum, zpow_rpow_half _ (Nat.cast_nonneg _)]
    push_cast; rfl
  have key : (((μS * μT⁻¹) (GeneralLinearGroup.det (j * mtor ϖ (indic s))) : ℂˣ) : ℂ) *
      (((μT⁻¹ (GeneralLinearGroup.det (j * mtor ϖ (indic s))))⁻¹ : ℂˣ) : ℂ) =
      (μS (GeneralLinearGroup.det (j * mtor ϖ (indic s))) : ℂ) := by
    rw [← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, inv_mul_cancel_right]
  simp only [omTwo, om, Pi.smul_apply, smul_eq_mul, map_one, Units.val_one, one_mul, nabs_one, Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.mul_one]
  rw [hq, ← mul_assoc, ← mul_assoc, key, hμh, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

end GlobalTheory.TorusLeft
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNegIndic

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.TorusRightScalar

theorem det_mtor' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GeneralLinearGroup.det (mtor ϖ e : GL (A ⊕ D) k) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, mtor, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ (Units.ne_zero ϖ), ih]

theorem sum_neg_indic {D : Type} [Fintype D] [DecidableEq D] (s : Finset D) :
    ∑ i, (-indic s) i = -(s.card : ℤ) := by
  simp [indic, Finset.sum_neg_distrib, Finset.sum_ite_mem]

theorem torusRight : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ μS μT : kˣ →* ℂˣ), IsUnram (μT * ξ⁻¹) → ∀ (s : Finset D) (j : GL (A ⊕ D) k), j ∈ parahoric k A D → ∀ (u : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) (y : Matrix (A ⊕ D') (A ⊕ D) k), omTwo μS μT (j * mtor ϖ (-indic s)) (1 : GL (A ⊕ D') k) u y = (((ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * (μT ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D')) * u (y * (j * mtor ϖ (-indic s)).1) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ μS μT hun s j hj u y
  have hjK : j ∈ KO k (A ⊕ D) := (mem_parahoric.1 hj).1
  have hn1 : nabs k (GeneralLinearGroup.det j) = 1 := nabs_det_of_mem_KO hjK
  have hv1 : valuation k ((GeneralLinearGroup.det j : kˣ) : k) = 1 := (nabs_eq_one_iff _).1 hn1
  have hxi : μT (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hun _ hv1
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
    exact this
  have hdet : GeneralLinearGroup.det (j * mtor ϖ (-indic s)) =
      GeneralLinearGroup.det j * ϖ ^ (-(s.card : ℤ)) := by
    rw [map_mul, det_mtor', sum_neg_indic]
  have hq0 : (0 : ℝ) < resCard k := by
    have q1 : 1 < Nat.card 𝓀[k] := Finite.one_lt_card
    unfold resCard; exact_mod_cast (lt_trans one_pos q1)
  have hnabs : nabs k (GeneralLinearGroup.det (j * mtor ϖ (-indic s))) = (resCard k : ℝ) ^ s.card := by
    rw [map_mul, show nabs k (GeneralLinearGroup.det j * GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) =
      nabs k (GeneralLinearGroup.det j) * nabs k (GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) by
        simp [nabs, map_mul], hn1, one_mul, mtor, nabs_det_torusElt hϖ, Fintype.sum_sum_type]
    simp [indic, Finset.sum_ite_mem]
  have hpow : ((resCard k : ℝ) ^ s.card) ^ ((Fintype.card (A ⊕ D') : ℝ) / 2) =
      (Real.sqrt (resCard k)) ^ (s.card * (Fintype.card A + Fintype.card D')) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le,
      ← Real.rpow_mul hq0.le, Fintype.card_sum]
    congr 1
    push_cast
    ring
  simp only [omTwo, om, map_one, inv_one, Units.val_one, one_smul, Matrix.one_mul, hnabs, hpow]
  have h1 : nabs k 1 = 1 := by simp [nabs]
  rw [h1, Real.one_rpow, hdet, map_mul, map_zpow, MonoidHom.inv_apply, MonoidHom.inv_apply, hxi]
  push_cast
  simp only [_root_.zpow_neg, zpow_natCast]
  rw [inv_pow, inv_inv]
  ring

end GlobalTheory.TorusRightScalar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTransferInvariantPairing

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTransfer

theorem transfer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → IsGen ρ' ξ ϖ (B.map (· * (μS ϖ * (μT ϖ)⁻¹)) + segL ϖ (μS ϖ) t) (b ⟨datum ξ⁻¹, hΦ⟩ x) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ t hD' ξ μS μT hξ hS hT W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb
  have hξi : IsTame ξ⁻¹ := fun y hy => by rw [MonoidHom.inv_apply, hξ y hy, inv_one]
  have hρ1 : ∀ y : X, ρ 1 y = y := fun y => by rw [map_one, Module.End.one_apply]
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine ⟨?_, ?_, fun s => ?_⟩
  · intro j hj d hd
    have h1 := hb 1 j ⟨datum ξ⁻¹, hΦ⟩ x
    rw [hρ1] at h1
    rw [← h1]
    have e : (⟨omTwo μS μT 1 j (datum ξ⁻¹), hW 1 j _ hΦ⟩ : W) = (ξ d : ℂ) • (⟨datum ξ⁻¹, hΦ⟩ : W) :=
      Subtype.ext (GlobalTheory.DatumEigenLeft.omTwo_datum_inv k A D D' ξ μS μT hξ hS j hj d hd)
    rw [e, map_smul, LinearMap.smul_apply]
  · simp [segL, hx2, hD']

  · intro R' d' hR'
    obtain ⟨hr1, hr2⟩ := GlobalTheory.ParHeckeReps.exists_reps_both k A D
    obtain ⟨-, hr2'⟩ := GlobalTheory.ParHeckeReps.exists_reps_both k A D'
    choose RR dd hRR using hr1
    choose RK hRK using hr2
    obtain ⟨RK', hRK'⟩ := hr2' (torusElt k D' ϖ (indic s))
    have hsn : ∀ n : ℕ, ∃ s : Finset D, n ≤ Fintype.card D → s.card = n := fun n => by
      by_cases h : n ≤ Fintype.card D
      · obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset D)) (by simpa using h)
        exact ⟨s, fun _ => hs⟩
      · exact ⟨∅, fun h' => absurd h' h⟩
    choose sn hsn using hsn
    have hq : (0 : ℝ) < (resCard k : ℝ) := by
      have : 0 < Nat.card 𝓀[k] := Nat.card_pos
      unfold resCard; exact_mod_cast this
    have hsq : ((Real.sqrt (resCard k) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hq).ne'
    set Φw : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦw
    set C : ℂ := (μS ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) with hC
    set cn : ℕ → ℂ := fun n => if n ≤ s.card then ((resCard k ^ (n * (t - (s.card - n))) * Formalism.L2.Col.gaussBin (resCard k) t (s.card - n) : ℕ) : ℂ) else 0 with hcn
    set den : ℕ → ℂ := fun n => (μT ϖ : ℂ) ^ n * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n * (Fintype.card A + Fintype.card D')) with hden
    have hden0 : ∀ n, den n ≠ 0 := fun n => mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (pow_ne_zero _ hsq)
    have key : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • (⟨omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) =
        C • ∑ n ∈ Finset.range (Fintype.card D + 1), (cn n * (den n)⁻¹) •
            ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) •
              (⟨omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) := by
      apply Subtype.ext
      funext y
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hT1 := GlobalTheory.ParHeckeTarget.sum_reps_datum_eq k A D D' ϖ hϖ ξ⁻¹ hξi s R' d' hR' RK' hRK' y
      have hU := GlobalTheory.ParHecke.heckeIdentity_integral k D D' ϖ hϖ t hD' s RK' hRK' sn (fun n => RK (torusElt k D ϖ (-indic (sn n))))
        (fun n hn => ⟨hsn n hn, hRK _⟩) (schur y)
      have hL : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) * omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹) y =
          C * (datum ξ⁻¹ y * ∑ g ∈ RK', intInd (((g⁻¹ : GL D' k)).1 * schur y)) := by
        have e2 : datum ξ⁻¹ y * ∑ g ∈ RK', intInd (((g⁻¹ : GL D' k)).1 * schur y) =
            ∑ g ∈ RK', liftS ξ⁻¹ (fun z => intInd ((g⁻¹).1 * z)) y := by
          rw [Finset.mul_sum]; rfl
        rw [e2, ← hT1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [GlobalTheory.TorusLeft.omTwo_torusLeft k A D D' ϖ hϖ ξ μS μT hS s j (hR'.1 j hj).1]
        simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hC]
        field_simp
      have hR : ∀ n ∈ Finset.range (Fintype.card D + 1),
          (cn n * (den n)⁻¹) * ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) *
              omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹) y =
            cn n * (datum ξ⁻¹ y * ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), intInd (schur y * g.1)) := by
        intro n hn
        have hc := hsn n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
        have e2 : datum ξ⁻¹ y * ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), intInd (schur y * g.1) =
            ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), liftS ξ⁻¹ (fun z => intInd (z * g.1)) y := by
          rw [Finset.mul_sum]; rfl
        rw [e2, ← GlobalTheory.ParHeckeSource.sum_reps_datum_eq k A D D' ϖ hϖ ξ⁻¹ hξi (sn n) _ _ (hRR _) _ (hRK _) y, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [GlobalTheory.TorusRightScalar.torusRight k A D D' ϖ hϖ ξ μS μT hT (sn n) j ((hRR _).1 j hj).1, hc]
        have := hden0 n
        simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hden] at this ⊢
        field_simp
      rw [hL, hU, Finset.sum_congr rfl hR]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have lhs : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • ρ' (j * mtor ϖ (indic s)) (b Φw x) =
        b (∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • (⟨omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W)) x := by

      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LinearMap.smul_apply, ← hb 1 _ Φw x, hρ1]
    have e4 : ∀ n ∈ Finset.range (Fintype.card D + 1),
        b ((cn n * (den n)⁻¹) • ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) •
              (⟨omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W)) x =
          (cn n * (den n)⁻¹ * genVal (resCard k) (Fintype.card A) (Fintype.card D) B n) • b Φw x := by
      intro n hn
      have hc := hsn n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))

      rw [map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply]
      simp_rw [map_smul, LinearMap.smul_apply]
      rw [GlobalTheory.ParHeckeTransfer.sum_eq_genVal k A D D' ϖ ξ μS μT hξ hT W hW hΦ X ρ x B ⟨hx1, hx2, hx3⟩ X' ρ' b hb (sn n) _ _ (hRR _), hc, smul_smul]

    rw [lhs, key, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl e4,
    ← Finset.sum_smul, smul_smul]
    congr 1
    have hN := GlobalTheory.ParHecke.StringEig.genVal_add_segL k ϖ hϖ (Fintype.card A) (Fintype.card D) t s.card B (μS ϖ) (μT ϖ) hx2
      (by rw [← hD']; exact Finset.card_le_univ s)
    rw [show Fintype.card D' = Fintype.card D + t from hD']
    rw [hN, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hC, hcn, hden, hD']
    ring

end GlobalTheory.ParHeckeTransfer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTransferInvariantPairingStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.lowerBlockParameter_transfer_invariantPairing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → IsGen ρ' ξ ϖ (B.map (· * (μS ϖ * (μT ϖ)⁻¹)) + segL ϖ (μS ϖ) t) (b ⟨datum ξ⁻¹, hΦ⟩ x) := by
  first | exact @GlobalTheory.ParHeckeTransfer.transfer | exact GlobalTheory.ParHeckeTransfer.transfer | (intros; apply GlobalTheory.ParHeckeTransfer.transfer <;> assumption)
end
end

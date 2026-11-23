module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ChangeDifferentiableOn
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Block
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableAtAdjugate
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralImageLeConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetBorSat
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetMulStrictLowerEqOne

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem det_mul_strictLower_eq_one (r : ℕ) (N : Matrix (Fin r) (Fin r) ℂ)
    (h0 : ∀ a c : Fin r, a < c → N a c = 0) (h1 : ∀ a, N a a = 1) :
    (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} =>
      if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0).det = 1 := by
  letI L : LinearOrder {p : Fin r × Fin r // p.2 < p.1} :=
    LinearOrder.lift' (fun p => toLex p.1) (fun p q h => Subtype.ext (toLex.injective h))
  have key := @Matrix.det_of_lowerTriangular {p : Fin r × Fin r // p.2 < p.1} ℂ _ _ _ L
    (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} =>
      if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0) (by
      intro p q hpq
      have hlt : toLex p.1 < toLex q.1 := hpq
      rw [Matrix.of_apply]
      split_ifs with h
      · rcases Prod.Lex.toLex_lt_toLex.1 hlt with h2 | ⟨_, h3⟩
        · exact h0 _ _ h2
        · exact absurd h (ne_of_lt h3)
      · rfl)
  rw [key]
  simp [h1]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetOfBlockTriangularInjective

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem det_of_blockTriangular_injective {m α R : Type} [Fintype m] [DecidableEq m]
    [LinearOrder α] [CommRing R] (M : Matrix m m R) (f : m → α) (hf : Function.Injective f)
    (h : M.BlockTriangular f) : M.det = ∏ i, M i i := by
  letI : LinearOrder m := LinearOrder.lift' f hf
  exact Matrix.det_of_upperTriangular (M := M) (fun i j hij => h hij)

theorem prod_lowerPairs_fst {r : ℕ} (d : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, d p.1.1 = ∏ a, d a ^ (a : ℕ) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1)
    (by simp) (fun p => d p.1), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [← Fin.card_Iio a]
  congr 1
  ext c; simp

theorem prod_lowerPairs_snd {r : ℕ} (d : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, d p.1.2 = ∏ a, d a ^ (r - 1 - (a : ℕ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1)
    (by simp) (fun p => d p.2), Finset.prod_filter, Fintype.prod_prod_type_right]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [← Fin.card_Ioi a]
  congr 1
  ext c; simp

theorem det_conj_strictLower : (∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℂ), B.det ≠ 0 → (∀ a c : Fin r, c < a → B a c = 0) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2).det = ∏ a : Fin r, B a a ^ (2 * (a : ℤ) - ((r : ℤ) - 1))) := by
  intro r B hdet htri
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hu
  have hB : B.BlockTriangular id := fun a c h => htri a c h
  have hBi : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  have hdiag : ∀ a, B a a * B⁻¹ a a = 1 := by
    intro a
    have h1 : (B * B⁻¹) a a = 1 := by rw [Matrix.mul_nonsing_inv B hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · exact h1
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [htri a c h, zero_mul]
      · rw [hBi (i := c) (j := a) h, mul_zero]
    · simp
  have hne : ∀ a, B a a ≠ 0 := fun a => left_ne_zero_of_mul_eq_one (hdiag a)
  have hinv : ∀ a, B⁻¹ a a = (B a a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (hdiag a)
  rw [det_of_blockTriangular_injective _
    (fun p : {p : Fin r × Fin r // p.2 < p.1} => toLex (p.1.1, OrderDual.toDual p.1.2))]
  · simp only [Matrix.of_apply, hinv]
    rw [Finset.prod_mul_distrib, prod_lowerPairs_fst (fun a => B a a),
      prod_lowerPairs_snd (fun a => (B a a)⁻¹), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hne a)]
    congr 1
    have := a.2
    omega
  · intro p q h
    have h' := toLex.injective h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h'
    exact Subtype.ext (Prod.ext h'.1 h'.2)
  · intro p q h
    simp only [Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] at h
    rcases h with h | ⟨_, h⟩
    · simp [htri _ _ h]
    · simp [hBi (i := q.1.2) (j := p.1.2) h]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeOfSection

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameSplit

theorem lintegral_le_of_section {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    [ProperSpace A] [ProperSpace B]
    (μ : Measure A) [μ.IsAddHaarMeasure] (ν : Measure B) [ν.IsAddHaarMeasure]
    (L : A → B) (hL : Continuous L) (hadd : ∀ x y, L (x + y) = L x + L y)
    (s : B → A) (hs : ∀ b, L (s b) = b) (S : Set A) (hS : MeasurableSet S)
    (hinv : ∀ b x, s b + x ∈ S ↔ x ∈ S)
    (hb : ∀ C : ℝ, ∃ D : ℝ, ∀ x ∈ S, ‖L x‖ ≤ C → ‖x‖ ≤ D) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : B → ℝ≥0∞, Measurable g →
      ∫⁻ y in S, g (L y) ∂μ ≤ K * ∫⁻ z, g z ∂ν := by
  have hLm : Measurable L := hL.measurable
  set ρ : Measure B := (μ.restrict S).map L with hρ
  have happ : ∀ T : Set B, MeasurableSet T → ρ T = μ (L ⁻¹' T ∩ S) := by
    intro T hT
    rw [hρ, Measure.map_apply hLm hT, Measure.restrict_apply (hLm hT)]
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun T hT => ?_⟩
    obtain ⟨C, hC⟩ := hT.isBounded.exists_norm_le
    obtain ⟨D, hD⟩ := hb C
    rw [happ T hT.measurableSet]
    refine lt_of_le_of_lt (measure_mono (t := Metric.closedBall 0 D) ?_)
      (isCompact_closedBall (0 : A) D).measure_lt_top
    intro x hx
    simpa using hD x hx.2 (hC _ hx.1)
  haveI : ρ.IsAddLeftInvariant := by
    refine ⟨fun b => ?_⟩
    ext T hT
    have hm : Measurable fun z : B => b + z := (continuous_const.add continuous_id).measurable
    rw [Measure.map_apply hm hT, happ _ (hm hT), happ _ hT,
      ← measure_preimage_add μ (s b) (L ⁻¹' T ∩ S)]
    congr 1
    ext x
    simp [hadd, hs, hinv]
  refine ⟨(ρ.addHaarScalarFactor ν : ℝ≥0∞), ENNReal.coe_lt_top, fun g hg => le_of_eq ?_⟩
  rw [← lintegral_map hg hLm, ← hρ]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ρ ν]
  rw [lintegral_smul_measure]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem frameSplit : (∀ (r : ℕ) (X : Data E r) (R : ℝ), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : V (nd X) → ℝ≥0∞, Measurable g → ∫⁻ y in {y : Frame X.Ψ r | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R}, g (WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1 ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2) ≤ K * ∫⁻ z, g z) := by
  intro r X R
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := inferInstance
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI h3 : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  refine lintegral_le_of_section (volume : Measure (Frame X.Ψ r)) (volume : Measure (V (nd X)))
    (fun y => WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1
      ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2)
    ?_ ?_
    (fun z τ a c => if h : c < a then z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) else 0)
    ?_ _ ?_ ?_ ?_
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    fun_prop
  · intro x y
    ext j
    simp
  · intro z
    ext j
    have h := ((Fintype.equivFin (Ent X)).symm j).2.2
    simp only [dif_pos h]
    exact congrArg (fun k => z k) ((Fintype.equivFin (Ent X)).apply_symm_apply j)
  · apply IsClosed.measurableSet
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    fun_prop
  · intro z x
    simp only [Set.mem_setOf_eq, Pi.add_apply]
    refine forall_congr' fun τ => forall_congr' fun a => forall_congr' fun c =>
      forall_congr' fun h => ?_
    rw [dite_eq_right h, zero_add]
  · intro C
    refine ⟨max (max C R) 0, fun x hx hC => ?_⟩
    have h0 : 0 ≤ max (max C R) 0 := le_max_right _ _
    refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun a =>
      (pi_norm_le_iff_of_nonneg h0).2 fun c => ?_
    by_cases h : c < a
    · have := (PiLp.norm_apply_le _ ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).trans hC
      have h' : ‖x τ a c‖ ≤ C := by
        have e := (Fintype.equivFin (Ent X)).symm_apply_apply ⟨τ, ⟨(a, c), h⟩⟩
        simp only at this
        erw [e] at this
        exact this
      exact h'.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hx τ a c h).trans ((le_max_right _ _).trans (le_max_left _ _))

end GlobalTheory.FrameSplit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameMeasureClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kapGG_holds : KapGGStatement (E := E) :=
  GlobalTheory.UnitriJac.kapGG_of_det GlobalTheory.det_conj_strictLower GlobalTheory.det_mul_strictLower_eq_one

theorem measInv_holds : MeasInvStatement (E := E) :=
  GlobalTheory.measInv_of_jacobian kapGG_holds GlobalTheory.NormFactor.nfac_transform

theorem frameMeas_holds : FrameMeasStatement (E := E) :=
  GlobalTheory.FrameMeas.frameMeas_of_local measInv_holds
    (GlobalTheory.frame_measure_local GlobalTheory.FrameSplit.frameSplit)

theorem extF_holds : ExtFStatement (E := E) :=
  extF_of lu_holds frameMeas_holds

theorem measure_statements :
    (KapGGStatement (E := E)) ∧ (MeasInvStatement (E := E)) ∧ (FrameMeasStatement (E := E)) ∧
      (ExtFStatement (E := E)) :=
  ⟨kapGG_holds, measInv_holds, frameMeas_holds, extF_holds⟩

end GlobalTheory.FrameMeasureClosed
end
end

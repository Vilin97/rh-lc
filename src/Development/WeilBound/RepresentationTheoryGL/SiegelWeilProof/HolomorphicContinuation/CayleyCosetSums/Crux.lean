module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperatorsAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AnalyticAtInverseFirstBlock
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdProps
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DpDual
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
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Aesop.Main
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IteratedFDerivMulConstOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FzSliceContDiffOn
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FzSliceContDiffOn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjSt
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecondUnitaryBlockOfPair
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulConjTransposeEq
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphU
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.VacuumNonvanishingOfFacts

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetUnitOfInK

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem det_nU (H : Matrix (Fin n) (Fin n) ℂ) : (nU H).det = 1 := by
  simp [nU, Matrix.det_fromBlocks_zero₂₁]

theorem fz_twist (m : ℕ) (e : ℤ) (z : ℂ) (y : M2 n) : fz m e z y = y.det ^ e * fz m 0 z y := by
  simp [fz, mul_assoc]

theorem det_unit_of_inK {k : M2 n} (hk : InK k) : star k.det * k.det = 1 := by
  have h := congrArg Matrix.det hk.2
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  exact h

theorem rhoP_twist {Kg : Type} (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (k : Kg) : rhoP ι m e Y k * (ι k).det ^ e = rhoP ι m 0 Y k := by
  unfold rhoP
  rw [fz_twist m e 0 (ι k)]
  simp only [star_mul, star_zpow₀]
  have hu : star (ι k).det * (ι k).det = 1 := det_unit_of_inK (hK k)
  have h1 : star (ι k).det ^ e * (ι k).det ^ e = 1 := by
    rw [← mul_zpow, hu, _root_.one_zpow]
  linear_combination (star ((u2 (ι k))⁻¹ * Y * u1 (ι k)).trace * star (fz m 0 0 (ι k))) * h1

theorem tOp_twist {Kg : Type} [MeasurableSpace Kg] (μ : Measure Kg) (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ)
    (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n) (z : ℂ) :
    tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) x =
      (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ ι (rhoP ι m 0 Y) ψ a b (fz m 0 z) x := by
  unfold tOp
  rw [← integral_const_mul]
  congr 1
  funext k
  have hin : (∫ (t : Fin n → Fin n → ℝ), fz m e z (x * ι k * a * nU (herm t) * b) * ψ t)
      = (x.det ^ e * (ι k).det ^ e * a.det ^ e * b.det ^ e) *
        ∫ (t : Fin n → Fin n → ℝ), fz m 0 z (x * ι k * a * nU (herm t) * b) * ψ t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [fz_twist m e z, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one,
      mul_zpow, mul_zpow, mul_zpow]
    ring
  rw [hin, ← rhoP_twist ι hK m e Y k]
  ring

theorem eRed : ERed := by
  intro h n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hK
  obtain ⟨P, ψ, a, b, x, h1, h2, h3, h4, h5⟩ := h n m hmn Kg μ ι hι hK
  refine ⟨P, ψ, a, b, x, h1, h2, h3, h4, ?_⟩
  have hKk : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hfun : (fun z : ℂ => tOp μ (⇑ι) (rhoP (⇑ι) m e P) ψ a b (fz m e z) x)
      = fun z : ℂ => (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ (⇑ι) (rhoP (⇑ι) m 0 P) ψ a b (fz m 0 z) x := by
    funext z
    exact tOp_twist μ ι hKk m e P ψ a b x z
  rw [hfun, deriv_const_mul_field']
  refine mul_ne_zero ?_ h5
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact zpow_ne_zero _ (isUnit_det_of_InG h4).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h2).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h3).ne_zero

end PositivityTheory.Rg.Sw.HSt
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdAnalytic

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem Fd_analytic (m : ℕ) : AnalyticOnNhd ℂ (Fd (n := n) m) (DomZ n) := by
  letI : TopologicalSpace (M2 n) := (inferInstance : NormedAddCommGroup (M2 n)).toMetricSpace.toUniformSpace.toTopologicalSpace
  have hU := (fzHol n m 0).2.2
  intro y hy
  have h1 : AnalyticAt ℂ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0)) (0, y) :=
    (ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : M2 n))).analyticAt _ |>.comp (hU.fderiv (0, y) ⟨Set.mem_univ _, hy⟩)
  have hl : AnalyticAt ℂ (fun w : M2 n => ((0 : ℂ), w)) y := analyticAt_const.prod analyticAt_id
  have h2 := h1.comp hl
  refine h2.congr ?_
  filter_upwards [isOpen_domZ.mem_nhds hy] with w hw
  exact (Fd_eq m hw).symm

theorem fdProps : FdProps := by
  intro n m
  refine ⟨(Fd_analytic m).contDiffOn_of_completeSpace, ?_⟩
  intro Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ hψs ha hb hx
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  set y : Kg × (Fin n → Fin n → ℝ) → M2 n := fun p => x * ι p.1 * a * nU (herm p.2) * b with hydef
  have hherm : Continuous (herm (n := n)) := by unfold herm; fun_prop
  have hnU : Continuous fun t : Fin n → Fin n → ℝ => nU (herm t) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hy : Continuous y :=
    (((continuous_const.mul (hι.comp continuous_fst)).mul continuous_const).mul (hnU.comp continuous_snd)).mul
      continuous_const
  have hyD : ∀ p, y p ∈ DomZ n := fun p =>
    gset_sub_domZ (inG_mul (inG_mul (inG_mul (inG_mul hx (hιG p.1)) ha) (inG_nU_herm p.2)) hb)
  set U : ℂ × M2 n → ℂ := fun q => fz m 0 q.1 q.2 with hUdef
  have hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n) := fz_contDiffOn m
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod isOpen_domZ
  set U' : ℂ × M2 n → ℂ := fun q => fderiv ℂ U q (1, 0) with hU'def
  have hU' : ContinuousOn U' (Set.univ ×ˢ DomZ n) :=
    ((hU.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const).continuousOn
  set F : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U (z, y p) * ψ p.2) with hFdef
  set F' : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U' (z, y p) * ψ p.2) with hF'def
  set S : Set (Kg × (Fin n → Fin n → ℝ)) := Set.univ ×ˢ tsupport ψ with hSdef
  have hS : IsCompact S := isCompact_univ.prod hψs
  have hzero : ∀ p, p ∉ S → ψ p.2 = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (fun h => hp ⟨Set.mem_univ _, h⟩)
  have hFc : ∀ z, Continuous (F z) := fun z =>
    (hρ.comp continuous_fst).mul ((hU.continuousOn.comp_continuous (continuous_const.prodMk hy)
      (fun p => ⟨Set.mem_univ _, hyD p⟩)).mul (hψ.comp continuous_snd))
  have hF'c : Continuous fun q : ℂ × (Kg × (Fin n → Fin n → ℝ)) => F' q.1 q.2 :=
    (hρ.comp (continuous_fst.comp continuous_snd)).mul ((hU'.comp_continuous (continuous_fst.prodMk
      (hy.comp continuous_snd)) (fun q => ⟨Set.mem_univ _, hyD q.2⟩)).mul (hψ.comp (continuous_snd.comp continuous_snd)))
  have hsupp : ∀ (G : Kg × (Fin n → Fin n → ℝ) → ℂ), Continuous G → (∀ p, p ∉ S → G p = 0) →
      Integrable G (μ.prod volume) := by
    intro G hG h0
    refine hG.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset hS (isClosed_tsupport G) ?_)
    refine closure_minimal (fun p hp => ?_) (isClosed_univ.prod (isClosed_tsupport ψ))
    by_contra h; exact hp (h0 p h)
  have hFi : ∀ z, Integrable (F z) (μ.prod volume) := fun z =>
    hsupp _ (hFc z) (fun p hp => by simp [hFdef, hzero p hp])
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1 |>.prod hS).exists_bound_of_continuousOn hF'c.continuousOn
  have hbound_int : Integrable (S.indicator fun _ => C) (μ.prod volume) :=
    (integrable_indicator_iff (isClosed_univ.prod (isClosed_tsupport ψ)).measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.prod volume) (F := F) (F' := F')
    (x₀ := (0 : ℂ)) (s := Metric.ball 0 1) (bound := S.indicator fun _ => C) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun z => (hFc z).aestronglyMeasurable) (hFi 0)
    ((hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p z hz => by
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]
        exact hC (z, p) ⟨Metric.ball_subset_closedBall hz, hp⟩
      · rw [Set.indicator_of_notMem hp]
        simp [hF'def, hzero p hp])
    hbound_int
    (Filter.Eventually.of_forall fun p z _ => by
      have hd : DifferentiableAt ℂ U (z, y p) :=
        (hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hyD p⟩)).differentiableAt (by simp)
      have hl : HasDerivAt (fun z' : ℂ => (z', y p)) ((1 : ℂ), (0 : M2 n)) z :=
        (hasDerivAt_id z).prodMk (hasDerivAt_const z (y p))
      have h1 := hd.hasFDerivAt.comp_hasDerivAt z hl
      exact (h1.mul_const (ψ p.2)).const_mul (ρ p.1))
  have hT : ∀ (G : M2 n → ℂ), (Integrable (fun p : Kg × (Fin n → Fin n → ℝ) => ρ p.1 * (G (y p) * ψ p.2))
      (μ.prod volume)) → tOp μ ι ρ ψ a b G x = ∫ p, ρ p.1 * (G (y p) * ψ p.2) ∂(μ.prod volume) := by
    intro G hG
    rw [integral_prod _ hG]
    unfold tOp
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hydef]
    exact (integral_const_mul _ _).symm
  have e1 : (fun z => tOp μ ι ρ ψ a b (fz m 0 z) x) = fun z => ∫ p, F z p ∂(μ.prod volume) := by
    funext z; exact hT (fz m 0 z) (hFi z)
  have e2 : ∫ p, F' 0 p ∂(μ.prod volume) = tOp μ ι ρ ψ a b (Fd m) x := by
    have hF'0 : F' 0 = fun p => ρ p.1 * (Fd m (y p) * ψ p.2) := by
      funext p; simp only [hF'def, hU'def, Fd_eq m (hyD p)]; rfl
    rw [hF'0, hT (Fd m) (hF'0 ▸ hderiv.1)]
  rw [e1, hderiv.2.deriv, e2]

end PositivityTheory.Rg.Sw.HSt
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.KsTraceSingle

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem ks_inv_eq {U : Matrix (Fin n) (Fin n) ℂ} (h : U * Uᴴ = 1) : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h

theorem ks_trace_single (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : (X * Matrix.single a b 1).trace = X b a := by
  rw [Matrix.trace_mul_single]
  simp

theorem ks_rhoP {Kg : Type} [Group Kg] (ι : Kg →* M2 n) (m : ℕ) (k k1 : Kg) (hk : InK (ι k))
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : N ∈ unitaryGroup (Fin n) ℂ) (h1 : ι k1 = Proj.kM 1 N) :
    rhoP ι m 0 1 (k * k1) = fV (m : ℤ) 0 (ι k) * ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
  obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) N (one_mem _) hN
  have hu1 : u1 (ι (k * k1)) = u1 (ι k) := by
    rw [map_mul, h1, ← hmk, first_block_mul_compact (ι k) hkk, hmk, Proj.first_unitary_block_of_pair, Matrix.mul_one]
  have hu2 : u2 (ι (k * k1)) = u2 (ι k) * N := by
    rw [map_mul, h1, ← hmk, second_block_mul_compact (ι k) hkk, hmk, Proj.second_unitary_block_of_pair]
  have U1 : u1 (ι k) * (u1 (ι k))ᴴ = 1 := first_cayley_block_unitary hk
  have U2 : u2 (ι k) * (u2 (ι k))ᴴ = 1 := second_cayley_block_unitary hk
  have UN : N * Nᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hN
    rwa [Matrix.star_eq_conjTranspose] at this
  have hfz : fz m 0 0 (ι (k * k1)) = (u1 (ι k)).det ^ (-(m : ℤ)) := by
    simp only [fz, zpow_zero, one_mul, neg_zero, Complex.cpow_zero, mul_one, hu1]
  have hne : (u1 (ι k)).det ≠ 0 := det_first_cayley_block_ne_zero hk.1
  have hd : star (u1 (ι k)).det = ((u1 (ι k)).det)⁻¹ := by
    have := congrArg Matrix.det U1
    rw [det_mul, det_one, det_conjTranspose] at this
    exact eq_inv_of_mul_eq_one_right this
  have hfV : fV (m : ℤ) 0 (ι k) = star ((u1 (ι k)).det ^ (-(m : ℤ))) := by
    have h := scalar_section_mul_conjugate_section hk (m : ℤ) 0
    have hf0 : f0 (m : ℤ) 0 (ι k) = (u1 (ι k)).det ^ (-(m : ℤ)) := by simp [f0]
    rw [hf0] at h
    rw [star_zpow₀, hd, eq_inv_of_mul_eq_one_right h]
    rw [_root_.zpow_neg, _root_.zpow_neg, _root_.inv_zpow, inv_inv]
  have htr : star ((u2 (ι (k * k1)))⁻¹ * 1 * u1 (ι (k * k1))).trace = ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
    rw [hu1, hu2, Matrix.mul_one, Matrix.mul_inv_rev, ← Matrix.trace_conjTranspose, ks_inv_eq UN, ks_inv_eq U2,
      ks_inv_eq U1]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  unfold rhoP
  rw [star_mul', hfz, htr, hfV]

theorem ks_perm_unitary (a b : Fin n) : (Equiv.swap a b).permMatrix ℂ ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [PEquiv.toMatrix_apply, Matrix.one_apply]

theorem ks_diag_unitary (b : Fin n) :
    Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1) ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = b <;> simp [h]

theorem ks_single_eq (a b : Fin n) :
    Matrix.single a b (1 : ℂ) = (1 / 2 : ℂ) • (Equiv.swap a b).permMatrix ℂ +
      (1 / 2 : ℂ) • ((Equiv.swap a b).permMatrix ℂ * Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1)) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.single_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    smul_eq_mul]
  by_cases hj : j = b
  · subst hj
    by_cases hi : i = a
    · subst hi
      simp <;> norm_num
    · have : ¬ (Equiv.swap a j i = j) := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
        exact hi
      simp [this, Ne.symm hi]
  · simp only [hj, if_false]
    by_cases h : Equiv.swap a b i = j
    · simp only [h, if_true]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring
    · simp only [h, if_false]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring

theorem kSplit : KSplit := by
  intro n m a0 b0 Kg _ ι hK
  classical
  set Pm : Matrix (Fin n) (Fin n) ℂ := (Equiv.swap a0 b0).permMatrix ℂ with hPmdef
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if i = b0 then (1 : ℂ) else -1) with hDdef
  have hPm : Pm ∈ unitaryGroup (Fin n) ℂ := ks_perm_unitary a0 b0
  have hD : D ∈ unitaryGroup (Fin n) ℂ := ks_diag_unitary b0
  set Nl : Fin 2 → Matrix (Fin n) (Fin n) ℂ := ![Pm, Pm * D] with hNldef
  have hNl : ∀ l, Nl l ∈ unitaryGroup (Fin n) ℂ := by
    intro l
    fin_cases l
    · exact hPm
    · exact mul_mem hPm hD
  have hex : ∀ l, ∃ k1 : Kg, ι k1 = Proj.kM 1 (Nl l) := fun l => by
    obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) (Nl l) (one_mem _) (hNl l)
    have : InK (Proj.kM 1 (Nl l)) := by rw [← hmk]; exact hkk
    exact (hK _).1 this
  choose kl hkl using hex
  refine ⟨2, fun _ => 1 / 2, kl, fun k => ?_⟩
  have hk : InK (ι k) := (hK _).2 ⟨k, rfl⟩
  rw [Fin.sum_univ_two, ks_rhoP ι m k (kl 0) hk _ (hNl 0) (hkl 0), ks_rhoP ι m k (kl 1) hk _ (hNl 1) (hkl 1)]
  rw [← ks_trace_single ((u1 (ι k))⁻¹ * u2 (ι k)) a0 b0, ks_single_eq a0 b0]
  simp only [hNldef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

end PositivityTheory.Rg.Sw.HSt
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Crux

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.HSt

theorem crux : Crux := eRed (vacuum_nonvanishing_of_facts fdProps djFd kSplit sphU fzHol)

end PositivityTheory.Rg.Sw.HSt
end
end

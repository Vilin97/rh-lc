module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HermitianMatrixIdentities
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelThird
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Isometry
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ShearMp
import Mathlib.CategoryTheory.Countable
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelFourth

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.unitMultiplierModel

open Formalism.MainNotions.BigCellDensity Formalism.FourierDecayAlt.P.Dx2.Rad Formalism.L2.SG.monomialWeightModel

variable {r : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1))

local notation "W" => wPt pN

theorem mul_unit_mp (c : ℂ) (h : ‖c‖ = 1) : MeasurePreserving (fun z : ℂ => c * z) volume volume := by
  have hc : c ∈ Submonoid.unitSphere ℂ := by simp [Submonoid.unitSphere, h]
  have key := (rotation (⟨c, hc⟩ : Circle)).measurePreserving
  have e : (fun z : ℂ => c * z) = rotation (⟨c, hc⟩ : Circle) := by
    funext z; rfl
  rw [e]
  exact key

variable (d : Fin (r + 1) → ℂ)

theorem Rm_mp (hd : ∀ a, d a ≠ 0) (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W, ‖d (W q.1.1)‖ = ‖d (W q.1.2)‖) :
    MeasurePreserving (Rm pN d) volume volume := by
  have hsw : Function.Involutive (sw pN) := by
    intro q
    exact Subtype.ext (Prod.ext (wPt_invol pN q.1.1) (wPt_invol pN q.1.2))
  let e : Formalism.FourierDecayAlt.C2.Lstidx W ≃ Formalism.FourierDecayAlt.C2.Lstidx W :=
    ⟨sw pN, sw pN, hsw, hsw⟩
  have hG := volume_measurePreserving_piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm
  have h : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W,
      MeasurePreserving (fun z : ℂ => d (W q.1.1) / d (W q.1.2) * star z) volume volume := by
    intro q
    have hu : ‖d (W q.1.1) / d (W q.1.2)‖ = 1 := by
      rw [norm_div, hdm q, div_self]
      exact norm_ne_zero_iff.mpr (hd _)
    exact (mul_unit_mp _ hu).comp Complex.conjLIE.measurePreserving
  have hF := volume_preserving_pi h
  have heq : Rm pN d = (fun (a : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) (i : Formalism.FourierDecayAlt.C2.Lstidx W) =>
      d (W i.1.1) / d (W i.1.2) * star (a i)) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm) := by
    funext x q
    have hq := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) e.symm x (e q)
    rw [Equiv.symm_apply_apply] at hq
    change _ = x (sw pN q) at hq
    simp only [Rm, Function.comp_apply, hq]
  rw [heq]
  exact hF.comp hG

end Formalism.L2.SG.unitMultiplierModel

end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelSecond

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace Formalism.L2.SG.lowerTriangularModel

open Formalism.FourierDecayAlt.P.Dx2.Rad (low low_apply low_coord)

variable {m : ℕ} (w : Equiv.Perm (Fin m))

def ht (q : Formalism.FourierDecayAlt.C2.Lstidx w) : ℕ := q.1.1.val - q.1.2.val

theorem low_upper (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) (h : i < j) :
    low w y i j = 0 := by
  rw [low_apply, Matrix.one_apply_ne (ne_of_lt h), zero_add, dite_eq_right]
  rintro ⟨h1, -⟩
  exact absurd (lt_trans h1 h) (lt_irrefl _)

theorem low_diag (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i : Fin m) : low w y i i = 1 := by
  rw [low_apply, Matrix.one_apply_eq, dite_eq_right (fun h => lt_irrefl _ h.1), add_zero]

theorem low_bt (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) :
    (low w y).BlockTriangular OrderDual.toDual := by
  intro i j hij
  exact low_upper w y i j hij

theorem low_det (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : (low w y).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (low_bt w y)]
  exact Finset.prod_eq_one fun i _ => low_diag w y i

abbrev M (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ := (low w y)⁻¹

theorem isUnit_low (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : IsUnit (low w y).det := by
  rw [low_det]
  exact isUnit_one

theorem M_upper (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) (h : i < j) : M w y i j = 0 := by
  haveI := Matrix.invertibleOfIsUnitDet (low w y) (isUnit_low w y)
  exact Matrix.blockTriangular_inv_of_blockTriangular (low_bt w y) h

theorem mul_M (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : low w y * M w y = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_low w y)

theorem sum_split (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) :
    ∑ c, low w y i c * M w y c j =
      ∑ c ∈ Finset.univ.filter (fun c => j ≤ c ∧ c ≤ i), low w y i c * M w y c j := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rfl
  · rcases not_and_or.1 h with h1 | h1
    · rw [M_upper w y c j (not_le.1 h1), mul_zero]
    · rw [low_upper w y i c (not_le.1 h1), zero_mul]

theorem M_diag (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i : Fin m) : M w y i i = 1 := by
  have h := congrFun (congrFun (mul_M w y) i) i
  rw [Matrix.mul_apply, sum_split, Matrix.one_apply_eq] at h
  have e : Finset.univ.filter (fun c => i ≤ c ∧ c ≤ i) = {i} := by
    ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  rw [e, Finset.sum_singleton, low_diag, one_mul] at h
  exact h

theorem M_rec (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) (hji : j < i) :
    M w y i j + low w y i j =
      -∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), low w y i c * M w y c j := by
  have h := congrFun (congrFun (mul_M w y) i) j
  rw [Matrix.mul_apply, sum_split, Matrix.one_apply_ne (ne_of_gt hji)] at h
  have e : Finset.univ.filter (fun c => j ≤ c ∧ c ≤ i) =
      insert i (insert j (Finset.univ.filter (fun c => j < c ∧ c < i))) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h2 | h2
      · rcases h1.lt_or_eq with h1 | h1
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
        · exact Or.inr (Or.inl h1.symm)
      · exact Or.inl h2
    · rintro (h | h | h)
      · exact ⟨h ▸ hji.le, h ▸ le_rfl⟩
      · exact ⟨h ▸ le_rfl, h ▸ hji.le⟩
      · exact ⟨h.1.le, h.2.le⟩
  have hi : i ∉ insert j (Finset.univ.filter (fun c => j < c ∧ c < i)) := by
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
    exact ⟨ne_of_gt hji, fun h => lt_irrefl _ h.2⟩
  have hj : j ∉ Finset.univ.filter (fun c => j < c ∧ c < i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => lt_irrefl _ h.1
  rw [e, Finset.sum_insert hi, Finset.sum_insert hj, low_diag, one_mul, M_diag, mul_one] at h
  linear_combination h

theorem M_dep (n : ℕ) : ∀ (y y' : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ), (∀ q, ht w q ≤ n → y q = y' q) →
    ∀ i j : Fin m, i.val - j.val ≤ n → M w y i j = M w y' i j := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y y' hy i j hij
  rcases lt_trichotomy i j with h | h | h
  · rw [M_upper w y i j h, M_upper w y' i j h]
  · subst h; rw [M_diag, M_diag]
  · have hL : ∀ a b : Fin m, a.val - b.val ≤ n → low w y a b = low w y' a b := by
      intro a b hab
      rw [low_apply, low_apply]
      congr 1
      split_ifs with hq
      · exact hy _ hab
      · rfl
    have e1 := M_rec w y i j h
    have e2 := M_rec w y' i j h
    have hsum : ∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), low w y i c * M w y c j =
        ∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), low w y' i c * M w y' c j := by
      refine Finset.sum_congr rfl fun c hc => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have hc1 := Fin.lt_def.1 hc.1
      have hc2 := Fin.lt_def.1 hc.2
      rw [hL i c (by omega)]
      congr 1
      exact ih (c.val - j.val) (by omega) y y' (fun q hq => hy q (by omega)) c j le_rfl
    have := hL i j hij
    linear_combination e1 - e2 - this - hsum

def linv (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ := fun q => M w y q.1.1 q.1.2

theorem low_cont : Continuous (low w) := by
  have e : low w = fun y => Matrix.of fun i j =>
      (1 : Matrix (Fin m) (Fin m) ℂ) i j + if h : j < i ∧ w.symm i < w.symm j then y ⟨(i, j), h⟩ else 0 := by
    funext y; ext i j; exact low_apply w y i j
  rw [e]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_const.add (continuous_apply _)
  · exact continuous_const

theorem M_cont : Continuous (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => M w y) := by
  have e : (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => M w y) = fun y => (low w y).adjugate := by
    funext y
    show (low w y)⁻¹ = _
    rw [Matrix.inv_def, low_det, Ring.inverse_one, one_smul]
  rw [e]
  exact (low_cont w).matrix_adjugate

theorem linv_mp : MeasurePreserving (linv w) volume volume := by
  set τ : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx w, (Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) → ℂ := fun q y => -(M w y q.1.1 q.1.2 + y q) with hτ
  have hmeas : ∀ q, Measurable (τ q) := fun q => by
    refine Measurable.neg (Measurable.add ?_ (measurable_pi_apply q))
    exact ((continuous_apply q.1.2).comp ((continuous_apply q.1.1).comp (M_cont w))).measurable
  have hdep : ∀ q (x x' : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ), (∀ q', ht w q' < ht w q → x q' = x' q') → τ q x = τ q x' := by
    intro q x x' hx
    have hq := q.2.1
    have hq' := Fin.lt_def.1 hq
    simp only [hτ]
    congr 1
    have e1 := M_rec w x q.1.1 q.1.2 hq
    have e2 := M_rec w x' q.1.1 q.1.2 hq
    have hLq : ∀ y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ, low w y q.1.1 q.1.2 = y q :=
      fun y => low_coord w y q
    rw [hLq] at e1 e2
    rw [e1, e2]
    congr 1
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hc1 := Fin.lt_def.1 hc.1
    have hc2 := Fin.lt_def.1 hc.2
    have hL : low w x q.1.1 c = low w x' q.1.1 c := by
      rw [low_apply, low_apply]
      congr 1
      split_ifs with h
      · exact hx _ (by simp only [ht]; omega)
      · rfl
    rw [hL]
    congr 1
    exact M_dep w (c.val - q.1.2.val) x x' (fun q' hq'' => hx q' (by simp only [ht] at hq'' ⊢; omega)) c q.1.2 le_rfl
  have hS := Formalism.L2.SG.NGCut.SplitEmbedding.shear_mp _ (Formalism.FourierDecayAlt.C2.Lstidx w) rfl (fun _ => ℂ) (fun _ => volume) (ht w) τ hmeas hdep
  have hN := Measure.measurePreserving_neg (volume : Measure (Formalism.FourierDecayAlt.C2.Lstidx w → ℂ))
  have e : linv w = Neg.neg ∘ (fun g p => g p + τ p g) := by
    funext y q
    simp only [Function.comp_apply, Pi.neg_apply, hτ, linv]
    ring
  rw [e]
  exact hN.comp hS

end Formalism.L2.SG.lowerTriangularModel

end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelFifth

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.flagStabilizerModel

open Formalism.MainNotions.BigCellDensity Formalism.FourierDecayAlt.P.Dx2.Rad Formalism.L2.SG.monomialWeightModel Formalism.L2.SG.unitMultiplierModel

variable {r : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1))

local notation "W" => wPt pN

theorem mp_model {k0 : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r Wp Wq) {δ : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r}
    (hδ : δ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx (wPt pN),
      ‖d (wPt pN q.1.1)‖ = ‖d (wPt pN q.1.2)‖)
    (hZ : Zhat (k0 + 1) r Ds.z Ds.z' δ = Formalism.FourierDecayAlt.C2.monoP (wPt pN) d)
    (μ : Measure (Mt (k0 + 1) r))
    (hconc : μ {x | Matrix.of x ∉ Formalism.FourierDecayAlt.C6.Rset δ} = 0) (c : ℝ≥0∞)
    (hmap : μ.map (fun x => Formalism.MainNotions.S.rootCoords (k0 + 1) r Ds.z' pN (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ))) =
      c • volume) :
    μ = c • Formalism.FourierDecayAlt.D.muR Ds δ (wPt pN) := by
  have hzS : Formalism.FourierDecayAlt.C2.StdZ (k0 + 1) r Ds.z := ⟨Ds.z_mem, Ds.T_pos⟩
  have hz'S : Formalism.FourierDecayAlt.C2.StdZ (k0 + 1) r Ds.z' := ⟨Ds.z'_mem, Ds.T'_pos⟩
  have hG := good_of Ds hδ hd hZ
  have hu : IsUnit δ.det := ((uHGroup _ (Hpk (k0 + 1) r) Formalism.L2.SG.HermitianMatrixIdentities.hpk_isUnit).2.2 δ hδ).1
  have hδi : δ⁻¹ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := ((uHGroup _ (Hpk (k0 + 1) r) Formalism.L2.SG.HermitianMatrixIdentities.hpk_isUnit).2.2 δ hδ).2
  obtain ⟨Ds', hD1, hD2⟩ := Formalism.MainNotions.S.Pv.AmpDDPf.bsetting_of (k0 + 1) r (by omega) Ds.z' Ds.z hz'S hzS
  set d' : Fin (r + 1) → ℂ := fun a => star (d (W a)) with hd'def
  have hd' : ∀ a, d' a ≠ 0 := fun a => star_ne_zero.2 (hd _)
  have hZ' : Zhat (k0 + 1) r Ds'.z Ds'.z' δ⁻¹ = Formalism.FourierDecayAlt.C2.monoP W d' := by
    ext i a
    rw [hD1, hD2, Formalism.L2.SG.Pf.RootHaarLoc.zhat_inv Ds.z Ds.z' hδ hu i a, hZ]
    simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply, hd'def]
    by_cases hai : a = W i
    · have hia : i = W a := by rw [hai, wPt_invol]
      rw [if_pos hai, if_pos hia]
      all_goals (try (rw [hai, wPt_invol]))
    · have hia : ¬ i = W a := fun h => hai (by rw [h, wPt_invol])
      rw [if_neg hai, if_neg hia, star_zero]
  have hG' := good_of Ds' hδi hd' hZ'

  set φ : Mt (k0 + 1) r → Formalism.FourierDecayAlt.C2.Lstidx W → ℂ := phi0 Ds W with hφ
  set φ' : Mt (k0 + 1) r → Formalism.FourierDecayAlt.C2.Lstidx W → ℂ :=
    fun x => phi0 Ds' W (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ)) with hφ'
  have hφc : Continuous φ := continuous_radial_phi Ds
  have hφ'c : Continuous φ' := by
    refine (continuous_radial_phi Ds').comp ?_
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

  have hRinv : ∀ x : Mt (k0 + 1) r, Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset δ →
      δ⁻¹ * Matrix.of x * δ ∈ Formalism.FourierDecayAlt.C6.Rset δ⁻¹ := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    rw [Matrix.nonsing_inv_nonsing_inv _ hu]
    have : δ * (δ⁻¹ * Matrix.of x * δ) * δ⁻¹ = Matrix.of x := by
      simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [this]
    exact hx.1

  have hroot : ∀ x : Mt (k0 + 1) r, Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset δ →
      Formalism.MainNotions.S.rootCoords (k0 + 1) r Ds.z' pN (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ)) = Tmap pN (φ' x) := by
    intro x hx
    have hm := hRinv x hx
    have e2 := u_eq_low Ds' hδi hd' hG' hm
    have hρ := rhoF_unique Ds' hδi hd' hG' (φ' x) hm (by
      rw [← Matrix.conjTranspose_conjTranspose (Formalism.FourierDecayAlt.C2.uMap _ _ _ _), e2])
    have h1 := Formalism.L2.SG.Pf.RootHaarLoc.rootCoords_psiG Ds'.z Ds' rfl pN hδi hd' hZ' (Tmap pN (φ' x))
    rw [Tinv_Tmap, ← hρ, hD1] at h1
    exact h1

  have hkey : ∀ x : Mt (k0 + 1) r, Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset δ →
      φ x = Formalism.L2.SG.lowerTriangularModel.linv W (Rm pN d (φ' x)) := by
    intro x hx
    have hm := hRinv x hx
    have e1 := u_eq_low Ds hδ hd hG hx
    have e2 := u_eq_low Ds' hδi hd' hG' hm
    have zh := Formalism.L2.SG.HermitianMatrixIdentities.zhat_uMap hzS hz'S hδ hx.1 hx.2
    have hinv : Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z (Matrix.of x)⁻¹ = (Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z (Matrix.of x))⁻¹ := by
      have hxu : IsUnit (Matrix.of x).det := ((uHGroup _ (Hpk (k0 + 1) r) Formalism.L2.SG.HermitianMatrixIdentities.hpk_isUnit).2.2 _ hx.1.1).1
      have hm1 := uMap_mul Ds hx.1 (PI.WBL.Cv.n_inv hx.1)
      rw [Matrix.mul_nonsing_inv _ hxu, uMap_one _ hzS] at hm1
      exact (Matrix.inv_eq_right_inv hm1.symm).symm
    have e1' : (Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z (Matrix.of x))ᴴ = low W (φ x) := e1
    have e2' : (Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds'.z (δ⁻¹ * Matrix.of x * δ))ᴴ = low W (φ' x) := e2
    have hU : Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z (Matrix.of x) = (low W (φ x))ᴴ := by
      rw [← e1', Matrix.conjTranspose_conjTranspose]
    have hU' : Formalism.FourierDecayAlt.C2.uMap (k0 + 1) r Ds.z' (δ⁻¹ * Matrix.of x * δ) = (low W (φ' x))ᴴ := by
      rw [← hD1, ← e2', Matrix.conjTranspose_conjTranspose]
    rw [hU', hinv, hU, hZ, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose] at zh

    have h1 : low W (Rm pN d (φ' x)) * Formalism.FourierDecayAlt.C2.monoP W d = (low W (φ x))⁻¹ * Formalism.FourierDecayAlt.C2.monoP W d := by
      rw [low_R_mono pN d hd, zh]
    have h2 : low W (Rm pN d (φ' x)) = (low W (φ x))⁻¹ := by
      have := congrArg (· * Formalism.FourierDecayAlt.C2.monoP (wPt pN).symm (fun j => (d ((wPt pN).symm j))⁻¹)) h1
      simp only [Matrix.mul_assoc, mono_mul_inv pN d hd, Matrix.mul_one] at this
      exact this
    have hlu : IsUnit (low W (φ x)).det := Formalism.L2.SG.lowerTriangularModel.isUnit_low W _
    have h3 : low W (φ x) = (low W (Rm pN d (φ' x)))⁻¹ := by
      rw [h2, Matrix.nonsing_inv_nonsing_inv _ hlu]
    funext q
    rw [← low_coord W (φ x) q, h3]
    rfl

  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset δ := ae_iff.2 hconc
  have hB : μ.map φ' = c • volume := by
    have hA : μ.map (Tmap pN ∘ φ') = c • volume := by
      rw [← hmap]
      refine Measure.map_congr ?_
      filter_upwards [hae] with x hx
      exact (hroot x hx).symm
    have hTm : Measurable (Tmap pN) := (Tmap_mp pN).measurable
    have e : φ' = Tinv pN ∘ (Tmap pN ∘ φ') := by
      funext x; simp [Tinv_Tmap]
    have hTi := Tinv_mp pN
    rw [e, ← Measure.map_map hTi.measurable (hTm.comp hφ'c.measurable), hA,
      Measure.map_smul c hTi.aemeasurable, hTi.map_eq]
  have hC : μ.map φ = c • volume := by
    have hlinv := Formalism.L2.SG.lowerTriangularModel.linv_mp W
    have hR := Rm_mp pN d hd hdm
    rw [Measure.map_congr (g := Formalism.L2.SG.lowerTriangularModel.linv W ∘ Rm pN d ∘ φ') (by
      filter_upwards [hae] with x hx
      exact hkey x hx)]
    rw [← Measure.map_map hlinv.measurable (hR.measurable.comp hφ'c.measurable),
      ← Measure.map_map hR.measurable hφ'c.measurable, hB, Measure.map_smul c hR.aemeasurable, hR.map_eq,
      Measure.map_smul c hlinv.aemeasurable, hlinv.map_eq]
  have hrho := rhoF_meas Ds hδ hd hG
  have hD : μ = μ.map ((fun y => Matrix.of.symm (rhoF Ds δ W y)) ∘ φ) := by
    conv_lhs => rw [← Measure.map_id (μ := μ)]
    refine Measure.map_congr ?_
    filter_upwards [hae] with x hx
    have hρ := rhoF_unique Ds hδ hd hG (φ x) hx (by
      rw [← Matrix.conjTranspose_conjTranspose (Formalism.FourierDecayAlt.C2.uMap _ _ _ _), u_eq_low Ds hδ hd hG hx]
      rfl)
    show x = Matrix.of.symm (rhoF Ds δ W (φ x))
    rw [← hρ]
    rfl
  rw [hD, ← Measure.map_map hrho hφc.measurable, hC, Measure.map_smul c hrho.aemeasurable]
  rfl

end Formalism.L2.SG.flagStabilizerModel

end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelMeasure

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.ModelMeasure

open Formalism.MainNotions.BigCellDensity

theorem mp_modelK {r k : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1)) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {δ : Formalism.FourierDecayAlt.B.Mat k r} (hδ : δ ∈ Formalism.FourierDecayAlt.B.GV k r) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx (wPt pN), ‖d (wPt pN q.1.1)‖ = ‖d (wPt pN q.1.2)‖)
    (hZ : Zhat k r Ds.z Ds.z' δ = Formalism.FourierDecayAlt.C2.monoP (wPt pN) d) (μ : Measure (Mt k r))
    (hconc : μ {x | Matrix.of x ∉ Formalism.FourierDecayAlt.C6.Rset δ} = 0) (c : ℝ≥0∞)
    (hmap : μ.map (fun x => Formalism.MainNotions.S.rootCoords k r Ds.z' pN (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ))) = c • volume) :
    μ = c • Formalism.FourierDecayAlt.D.muR Ds δ (wPt pN) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt Ds.k_pos)
  exact Formalism.L2.SG.flagStabilizerModel.mp_model pN Ds hδ hd hdm hZ μ hconc c hmap

end Formalism.L2.SG.ModelMeasure

end
end
end

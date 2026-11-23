module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterA
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterB

section

@[expose] public section

open scoped ContDiff

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.ZI

variable (s : ℕ)

abbrev En : Type := (Fin s → ℂ) →L[ℝ] (Fin s → ℂ)

def act (Z : Fin s → Fin s → ℂ) : En s :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (Matrix.of Z).mulVec v
      map_add' := fun v w => Matrix.mulVec_add _ _ _
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }

theorem act_apply (Z : Fin s → Fin s → ℂ) (v : Fin s → ℂ) : act s Z v = (Matrix.of Z).mulVec v := rfl

def eA : (Fin s → Fin s → ℂ) →L[ℝ] En s :=
  LinearMap.toContinuousLinearMap
    { toFun := act s
      map_add' := fun Z Z' => by
        ext1 v
        simp only [act_apply, ContinuousLinearMap.add_apply]
        exact Matrix.add_mulVec _ _ _
      map_smul' := fun c Z => by
        ext1 v
        simp only [act_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        exact Matrix.smul_mulVec c (Matrix.of Z) v }

theorem eA_apply (Z : Fin s → Fin s → ℂ) (v : Fin s → ℂ) : eA s Z v = (Matrix.of Z).mulVec v := rfl

def invF (Z : Fin s → Fin s → ℂ) : Fin s → Fin s → ℂ := Matrix.of.symm (Matrix.of Z)⁻¹

theorem eA_mul_inv {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    eA s Z * eA s (invF s Z) = 1 ∧ eA s (invF s Z) * eA s Z = 1 := by
  have hu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr h
  have hinv : Matrix.of (invF s Z) = (Matrix.of Z)⁻¹ := Matrix.of.apply_symm_apply _
  constructor <;> ext1 v <;>
    simp only [ContinuousLinearMap.mul_apply, eA_apply, ContinuousLinearMap.one_apply,
      Matrix.mulVec_mulVec, hinv, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec]

theorem isUnit_eA {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) : IsUnit (eA s Z) :=
  ⟨⟨eA s Z, eA s (invF s Z), (eA_mul_inv s h).1, (eA_mul_inv s h).2⟩, rfl⟩

theorem inverse_eA {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    Ring.inverse (eA s Z) = eA s (invF s Z) := by
  exact Ring.inverse_unit ⟨eA s Z, eA s (invF s Z), (eA_mul_inv s h).1, (eA_mul_inv s h).2⟩

def lamL (a b : Fin s) (ε : Bool) (T : En s) : (Fin s → Fin s → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W => if ε then (T (fun c => W c b) a).re else (T (fun c => W c b) a).im
      map_add' := fun W W' => by
        have : (fun c => (W + W') c b) = (fun c => W c b) + (fun c => W' c b) := rfl
        rw [this, map_add (f := _)]
        cases ε <;> simp
      map_smul' := fun r W => by
        have : (fun c => (r • W) c b) = r • (fun c => W c b) := rfl
        rw [this, map_smul]
        cases ε <;> simp }

theorem lamL_apply (a b : Fin s) (ε : Bool) (T : En s) (W : Fin s → Fin s → ℂ) :
    lamL s a b ε T W = if ε then (T (fun c => W c b) a).re else (T (fun c => W c b) a).im := rfl

def lamF (i : Fin s × Fin s × Bool) : En s →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => lamL s i.1 i.2.1 i.2.2 T
      map_add' := fun T T' => by
        ext W; simp only [lamL_apply, ContinuousLinearMap.add_apply]
        cases i.2.2 <;> simp
      map_smul' := fun c T => by
        ext W; simp only [lamL_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        cases i.2.2 <;> simp }

def cF (i : Fin s × Fin s × Bool) (Z : Fin s → Fin s → ℂ) : (Fin s → Fin s → ℂ) →L[ℝ] ℝ :=
  lamF s i (Ring.inverse (eA s Z))

theorem cF_apply (i : Fin s × Fin s × Bool) {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0)
    (W : Fin s → Fin s → ℂ) :
    cF s i Z W = if i.2.2 then (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).re
      else (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).im := by
  have hinv : Matrix.of (invF s Z) = (Matrix.of Z)⁻¹ := Matrix.of.apply_symm_apply _
  rw [cF, inverse_eA s h]
  show lamL s i.1 i.2.1 i.2.2 (eA s (invF s Z)) W = _
  rw [lamL_apply, eA_apply, hinv]
  have e : ((Matrix.of Z)⁻¹.mulVec fun c => W c i.2.1) i.1
      = ((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1 := by
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
  rw [e]

theorem isOpen_det : IsOpen {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det (by exact continuous_id)) continuous_const

theorem contDiffOn_cF (i : Fin s × Fin s × Bool) (n : ℕ) :
    ContDiffOn ℝ n (cF s i) {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} := by
  have hinv : ContDiffOn ℝ n (Ring.inverse : En s → En s) {x | IsUnit x} := fun x hx => by
    obtain ⟨u, rfl⟩ := hx
    exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt
  exact (lamF s i).contDiff.comp_contDiffOn
    (hinv.comp (eA s).contDiff.contDiffOn (fun Z hZ => isUnit_eA s hZ))

theorem contDiffOn_inv (n : ℕ) : ContDiffOn ℝ n (Ring.inverse : En s → En s) {x : En s | IsUnit x} :=
  fun x hx => by
    obtain ⟨u, rfl⟩ := hx
    exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt

theorem norm_inverse_le {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    ‖Ring.inverse (eA s Z)‖ ≤ ‖eA s‖ * ‖invF s Z‖ := by
  rw [inverse_eA s h]
  exact (eA s).le_opNorm _

theorem cF_bound (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : Fin s → Fin s → ℂ, (Matrix.of Z).det ≠ 0 → ∀ i, ∀ a ≤ n,
    ‖iteratedFDeriv ℝ a (cF s i) Z‖ ≤ K * (max 1 ‖eA s‖ * max 1 ‖Ring.inverse (eA s Z)‖) ^ (a + 1) := by
  set U := {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} with hU_def
  have hUo : IsOpen U := isOpen_det s
  let φ : (Fin s → Fin s → ℂ) → En s := fun Z => Ring.inverse (eA s Z)
  let P : (En s →L[ℝ] En s) →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] En s) :=
    (ContinuousLinearMap.compL ℝ (Fin s → Fin s → ℂ) (En s) (En s)).flip (eA s)
  let Bi : En s →L[ℝ] En s →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] En s) :=
    (ContinuousLinearMap.compL ℝ (En s) (En s →L[ℝ] En s) _ (-P)).comp
      (ContinuousLinearMap.mulLeftRight ℝ (En s))
  have hφ : ∀ m : ℕ, ContDiffOn ℝ m φ U := fun m =>
    (contDiffOn_inv s m).comp (eA s).contDiff.contDiffOn (fun Z hZ => isUnit_eA s hZ)
  have hd : ∀ Z ∈ U, fderiv ℝ φ Z = Bi (φ Z) (φ Z) := by
    intro Z hZ
    obtain ⟨u, hu⟩ := isUnit_eA s hZ
    have h0 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at h0
    have h1 := h0.comp Z (eA s).hasFDerivAt
    have hinv : ((u⁻¹ : (En s)ˣ) : En s) = φ Z := by
      show _ = Ring.inverse (eA s Z)
      rw [← hu, Ring.inverse_unit u]
    rw [show φ = Ring.inverse ∘ (eA s) from rfl, h1.fderiv, hinv]
    ext W : 1
    simp only [Bi, P, φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      Function.comp_apply]
  obtain ⟨K0, hK0, hb⟩ := quad_bound Bi hUo hφ hd n
  refine ⟨(∑ j, ‖lamF s j‖) * K0,
    mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hK0, ?_⟩
  intro Z hZ i a ha
  have hZU : Z ∈ U := hZ
  have hcf : cF s i = (lamF s i) ∘ φ := rfl
  have e1 : iteratedFDeriv ℝ a (cF s i) Z = iteratedFDerivWithin ℝ a (cF s i) U Z :=
    (iteratedFDerivWithin_of_isOpen a hUo hZU).symm
  have e2 : iteratedFDeriv ℝ a φ Z = iteratedFDerivWithin ℝ a φ U Z :=
    (iteratedFDerivWithin_of_isOpen a hUo hZU).symm
  have h3 : ‖iteratedFDerivWithin ℝ a (cF s i) U Z‖
      ≤ ‖lamF s i‖ * ‖iteratedFDerivWithin ℝ a φ U Z‖ := by
    rw [hcf]
    exact (lamF s i).norm_iteratedFDerivWithin_comp_left (hφ a Z hZU) hUo.uniqueDiffOn hZU le_rfl
  have hLi : ‖lamF s i‖ ≤ ∑ j, ‖lamF s j‖ :=
    Finset.single_le_sum (f := fun j => ‖lamF s j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hM0 : 0 ≤ max 1 ‖φ Z‖ := le_trans zero_le_one (le_max_left _ _)
  have hM : max 1 ‖φ Z‖ ≤ max 1 ‖eA s‖ * max 1 ‖φ Z‖ :=
    le_mul_of_one_le_left hM0 (le_max_left _ _)
  have hL0 : 0 ≤ ∑ j, ‖lamF s j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [e1]
  calc _ ≤ ‖lamF s i‖ * ‖iteratedFDerivWithin ℝ a φ U Z‖ := h3
    _ ≤ (∑ j, ‖lamF s j‖) * (K0 * max 1 ‖φ Z‖ ^ (a + 1)) := by
        rw [← e2]
        exact mul_le_mul hLi (hb Z hZU a ha) (norm_nonneg _) hL0
    _ ≤ (∑ j, ‖lamF s j‖) * (K0 * (max 1 ‖eA s‖ * max 1 ‖φ Z‖) ^ (a + 1)) := by
        gcongr
    _ = (∑ j, ‖lamF s j‖) * K0 * (max 1 ‖eA s‖ * max 1 ‖Ring.inverse (eA s Z)‖) ^ (a + 1) := by
        ring

end PI.UnitaryGroupMassFormula.UsCost.ZI
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterC

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

theorem list_prod_le_pow (l : List ℝ) (lam : ℝ) (h : ∀ x ∈ l, 0 ≤ x ∧ x ≤ lam) :
    l.prod ≤ lam ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hp : 0 ≤ l.prod := List.prod_nonneg (fun y hy => (h y (List.mem_cons_of_mem x hy)).1)
    rw [List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul hx.2 ih' hp (hx.1.trans hx.2)

theorem max_one_le (c t : ℝ) (ht : 1 ≤ t) (x : ℝ) (hx : x ≤ c * t) : max 1 x ≤ (1 + |c|) * t := by
  have ht0 : 0 ≤ t := by linarith
  have h1 : c * t ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) ht0
  have h2 : 0 ≤ |c| * t := mul_nonneg (abs_nonneg c) ht0
  refine max_le ?_ ?_ <;> nlinarith

theorem zeta_cost_of_smooth_deriv (hS : ZSmooth) (hD : ZDeriv) (hDS : DirSize) : ZCost := by
  intro hSM hRP hSZ hDP hS21 k p s ρ σ d hd hs K hK hK0 q
  obtain ⟨C₁, hC₁⟩ := hDS hDP k p s ρ σ
  obtain ⟨C₂, hC₂⟩ := hS21 k p s ρ σ d hd hs K hK hK0
  obtain ⟨Kc, hKc0, hKc⟩ := ZI.cF_bound s q
  obtain ⟨C, hC1, hC⟩ := ZI.iter_words (V := G.Mat s) (I := Fin s × Fin s × Bool) q Kc hKc0
  have hE'0 : (0 : ℝ) ≤ max 1 ‖ZI.eA s‖ := zero_le_one.trans (le_max_left _ _)
  set A : ℝ := (1 + |(|C₁| * C₂ ^ 4)|) * (max 1 ‖ZI.eA s‖ * (1 + |‖ZI.eA s‖ * C₂|)) with hA
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (mul_nonneg hE'0 (by positivity))
  refine ⟨C * A ^ q, ?_⟩
  intro E _ _ H β hH ξ Z γ hZ hγ hKg hw
  have hZ' : (Matrix.of Z).det ≠ 0 := hZ
  refine ⟨(hS hSM hRP k p s ρ σ d hd E H q hH ξ Z γ hZ hγ).2.2, ?_⟩
  obtain ⟨hg1, -, hRn, -, -, -, hb, -, -, -, -, hinv⟩ := hC₂ ξ Z γ hγ hKg
  set g := gaXi k ρ σ d ξ Z γ with hg
  set lam := max 1 (C₁ * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) with hlam
  set M := max 1 ‖ZI.eA s‖ * max 1 ‖Ring.inverse (ZI.eA s Z)‖ with hM
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  have hβ : 0 ≤ β := by
    have := hw [] (by simp) (by simp)
    simp only [List.map_nil, List.prod_nil, mul_one] at this
    exact (norm_nonneg _).trans this
  have hlet : ∀ i, inLieP k (p + s) ρ (dirZ k ρ ξ i) ∧ lsz (dirZ k ρ ξ i) ≤ lam := fun i =>
    ⟨(hC₁ ξ i).1, (hC₁ ξ i).2.trans (le_max_right _ _)⟩
  have key := hC (α := B.Mat k (p + s + ρ)) (E := E)
    (fun b H' => B.CkOn (b : ℕ∞) (B.GV k (p + s + ρ)) H')
    (fun i H' => RdV (dirZ k ρ ξ i) H') (fun Z' => gaXi k ρ σ d ξ Z' γ)
    {Z' : G.Mat s | (Matrix.of Z').det ≠ 0} (fun i => ZI.cF s i) Z M lam
    (ZI.isOpen_det s) hZ' hM1 hlam1
    (fun b H' h => P.BetaSesquilinearity.CkOn_mono (by exact_mod_cast Nat.le_succ b) h)
    (fun b H' i h => by
      have h' : B.CkOn ((b : ℕ∞) + 1) (B.GV k (p + s + ρ)) H' := by simpa using h
      have := P.BetaSesquilinearity.CkOn_Dx (x := (false, dirZ k ρ ξ i)) (hlet i).1.1 h'
      simpa [P.BetaSesquilinearity.Dx] using this)
    (fun b H' h z hz => (hS hSM hRP k p s ρ σ d hd E H' b h ξ z γ hz hγ).2.2)
    (fun b H' h z hz => by
      ext1 W
      rw [hD hSM hRP hSZ k p s ρ σ d hd E H'
        (P.BetaSesquilinearity.CkOn_mono (by exact_mod_cast Nat.le_add_left 1 b) h) ξ z γ hz hγ W]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZI.cF_apply s i hz]
      rfl)
    (fun i n => ZI.contDiffOn_cF s i n)
    (fun i a ha => hKc Z hZ' i a ha)
    q le_rfl H β hH (fun w hwl => by
      have e : w.foldr (fun i H' => RdV (dirZ k ρ ξ i) H') H = B.Rw (w.map (dirZ k ρ ξ)) H := by
        simp [B.Rw, List.foldr_map]
      rw [e]
      refine (hw (w.map (dirZ k ρ ξ)) (fun X hX => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
          exact (hlet i).1) (by rw [List.length_map]; exact hwl)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hβ
      have := list_prod_le_pow ((w.map (dirZ k ρ ξ)).map lsz) lam (by
        intro x hx
        obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
        exact ⟨zero_le_one.trans (le_max_left _ _), (hlet i).2⟩)
      simpa using this)

  have hg0 : 0 ≤ B.gN g := by linarith
  have hR0 : 0 ≤ B.gN (Rn k (p + s) ρ ξ.1.2) := Real.sqrt_nonneg _
  have hlamb : lam ≤ (1 + |(|C₁| * C₂ ^ 4)|) * B.gN g ^ (2 * (p + s) + 2 * p) := by
    refine max_one_le _ _ (one_le_pow₀ hg1) _ ?_
    have h1 : B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 ≤ (C₂ * B.gN g ^ (p + s)) ^ 2 := pow_le_pow_left₀ hR0 hRn 2
    have h2 : (1 + ‖ξ.2.1.2‖) ^ 2 ≤ (C₂ * B.gN g ^ p) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
    have hpow : B.gN g ^ (2 * (p + s) + 2 * p) = (B.gN g ^ (p + s)) ^ 2 * (B.gN g ^ p) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    calc C₁ * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2
        = C₁ * (B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by ring
      _ ≤ |C₁| * (B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₁| * ((C₂ * B.gN g ^ (p + s)) ^ 2 * (C₂ * B.gN g ^ p) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) (abs_nonneg _)
      _ = (|C₁| * C₂ ^ 4) * B.gN g ^ (2 * (p + s) + 2 * p) := by rw [hpow]; ring
  have hMb : M ≤ max 1 ‖ZI.eA s‖ * ((1 + |‖ZI.eA s‖ * C₂|) * B.gN g ^ (p + s - 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hE'0
    refine max_one_le _ _ (one_le_pow₀ hg1) _ ?_
    calc ‖Ring.inverse (ZI.eA s Z)‖ ≤ ‖ZI.eA s‖ * ‖ZI.invF s Z‖ := ZI.norm_inverse_le s hZ'
      _ ≤ ‖ZI.eA s‖ * (C₂ * B.gN g ^ (p + s - 1)) := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = ‖ZI.eA s‖ * C₂ * B.gN g ^ (p + s - 1) := by ring
  have hLM : lam * M ≤ A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1)) := by
    calc lam * M ≤ ((1 + |(|C₁| * C₂ ^ 4)|) * B.gN g ^ (2 * (p + s) + 2 * p)) *
          (max 1 ‖ZI.eA s‖ * ((1 + |‖ZI.eA s‖ * C₂|) * B.gN g ^ (p + s - 1))) :=
          mul_le_mul hlamb hMb (by linarith) (by positivity)
      _ = A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1)) := by rw [hA, pow_add]; ring
  have hexp : (2 * (p + s) + 2 * p + (p + s - 1)) * q ≤ 5 * (p + s + ρ) * q :=
    Nat.mul_le_mul_right q (by omega)
  have hrp : B.gN g ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) = B.gN g ^ (5 * (p + s + ρ) * q) := by
    rw [← Real.rpow_natCast]; congr 1; push_cast; ring
  rw [hrp]
  calc ‖iteratedFDeriv ℝ q (fun Z' => H (gaXi k ρ σ d ξ Z' γ)) Z‖ ≤ C * β * (lam * M) ^ q := key
    _ ≤ C * β * (A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1))) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hLM q) (by positivity)
    _ = C * β * (A ^ q * B.gN g ^ ((2 * (p + s) + 2 * p + (p + s - 1)) * q)) := by rw [mul_pow, pow_mul]
    _ ≤ C * β * (A ^ q * B.gN g ^ (5 * (p + s + ρ) * q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg1 hexp) (by positivity))
          (by positivity)
    _ = C * A ^ q * β * B.gN g ^ (5 * (p + s + ρ) * q) := by ring

end PI.UnitaryGroupMassFormula.UsCost
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZCostOf

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

namespace PI.UnitaryGroupMassFormula.UsCost

theorem zCost_of (hS : ZSmooth) (hD : ZDeriv) (hDS : DirSize) : ZCost :=
  zeta_cost_of_smooth_deriv hS hD hDS

end PI.UnitaryGroupMassFormula.UsCost
end
end

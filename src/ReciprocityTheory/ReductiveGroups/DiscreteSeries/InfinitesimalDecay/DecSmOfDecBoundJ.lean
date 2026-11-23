module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic.Linter.Style

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.Bridge

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem br_facts {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) :
    P⁻¹ = Pᴴ ∧ P * Pᴴ = 1 ∧ Pᴴ * P = 1 ∧ Jm ε = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
  obtain ⟨⟨_, hJ⟩, hU⟩ := hP
  have h1 : P * Pᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : Pᴴ * P = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hU
    rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨Matrix.inv_eq_left_inv h2, h1, h2, ?_⟩
  have hJe : Jm ε = Formalism.REAL.Jm ε := rfl
  rw [hJe, ← hJ]
  calc Formalism.REAL.Jm ε = (P * Pᴴ) * Formalism.REAL.Jm ε * (P * Pᴴ) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by simp only [Matrix.mul_assoc]

theorem bridge_group {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ↔ P * g * P⁻¹ ∈ UJset ε := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have hJ' : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have key : ∀ Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Y * Pᴴ) * P = Y := fun Y => by
    calc Pᴴ * (P * Y * Pᴴ) * P = (Pᴴ * P) * Y * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  have e : (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = P * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * Pᴴ := by
    rw [hinv, ← hJ']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  show gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r ↔ inUJ ε (P * g * P⁻¹)
  unfold inUJ
  rw [e, hJ]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg (fun M => Pᴴ * M * P) h
    simp only [key] at this
    exact this

theorem bridge_lie {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.MainNotions.S.InLieHpk k r X ↔ inG ε (P * X * P⁻¹) := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have h2' : ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have key : ∀ Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Y * Pᴴ) * P = Y := fun Y => by
    calc Pᴴ * (P * Y * Pᴴ) * P = (Pᴴ * P) * Y * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  have e : (P * X * P⁻¹)ᴴ * Jm ε + Jm ε * (P * X * P⁻¹) =
      P * (Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X) * Pᴴ := by
    rw [hinv, hJ]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc, h2']
  show Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 ↔ inG ε (P * X * P⁻¹)
  unfold inG
  rw [e]
  constructor
  · intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    have := congrArg (fun M => Pᴴ * M * P) h
    simp only [key, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this

theorem bridge_gN {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g = Real.sqrt (S7.hs (P * g * P⁻¹)) := by
  obtain ⟨hi, h2, h1, -⟩ := br_facts hP
  have key : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Matrix.trace (Mᴴ * M)).re := by
    intro M
    rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  unfold Formalism.FourierDecayAlt.B.gN S7.hs
  congr 1
  have e1 : ∑ i, ∑ j, Complex.normSq (g i j) = ∑ i, ∑ j, ‖g i j‖ ^ 2 := by
    simp [Complex.normSq_eq_norm_sq]
  have e2 : (P * g * Pᴴ)ᴴ * (P * g * Pᴴ) = P * ((gᴴ * g) * Pᴴ) := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul]
  have L : ∑ i, ∑ j, ‖g i j‖ ^ 2 = (gᴴ * g).trace.re := key g
  have R : ∑ i, ∑ j, ‖(P * g * Pᴴ) i j‖ ^ 2 = ((P * g * Pᴴ)ᴴ * (P * g * Pᴴ)).trace.re := key _
  rw [e1, hi, L, R, e2, Matrix.trace_mul_comm P, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem bridge_smooth {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v : H) :
    v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ ↔ IsSmoothVecU ε (fun g => σ (P⁻¹ * g * P)) v := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have hPu : IsUnit P := hP.1.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  let cA : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ P⁻¹).comp (LinearMap.mulRight ℝ P))
  let cB : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ P).comp (LinearMap.mulRight ℝ P⁻¹))
  have hcA : ∀ g, cA g = P⁻¹ * g * P := fun g => by simp [cA, Matrix.mul_assoc]
  have hcB : ∀ g, cB g = P * g * P⁻¹ := fun g => by simp [cB, Matrix.mul_assoc]
  have hAB : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
  have hBA : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hPd, Matrix.mul_one]
  have hmem : ∀ g, Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) g ↔ inUJ ε (P * g * P⁻¹) := fun g => bridge_group hP g
  simp only [Formalism.MainNotions.S.smoothVecs, Set.mem_setOf_eq, Formalism.MainNotions.S.IsSmoothVec, IsSmoothVecU]
  constructor
  · intro hv g₀ hg₀
    have hg₁ : Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) (P⁻¹ * g₀ * P) := (hmem _).2 (by rw [hBA]; exact hg₀)
    obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hv _ hg₁
    refine ⟨cA ⁻¹' U, F ∘ cA, hU.preimage cA.continuous, by simp [hcA, hxU],
      hF.comp cA.contDiff.contDiffOn (fun x hx => hx), fun g hg hgJ => ?_⟩
    have hgH : Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) (P⁻¹ * g * P) := (hmem _).2 (by rw [hBA]; exact hgJ)
    have h3 := hfF _ (by simpa [hcA] using hg) hgH
    simp only at h3
    simp only [Function.comp_apply, hcA]
    exact h3
  · intro hv g₀ hg₀
    have hg₁ : inUJ ε (P * g₀ * P⁻¹) := (hmem g₀).1 hg₀
    obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hv _ hg₁
    refine ⟨cB ⁻¹' U, F ∘ cB, hU.preimage cB.continuous, by simp [hcB, hxU],
      hF.comp cB.contDiff.contDiffOn (fun x hx => hx), fun g hg hgH => ?_⟩
    have h3 := hfF _ (by simpa [hcB] using hg) ((hmem g).1 hgH)
    simp only at h3
    simp only [Function.comp_apply, hcB]
    rw [← h3, hAB]

theorem bridge_dsigW {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v =
      dSW (fun g => σ (P⁻¹ * g * P)) (w.map fun X => P * X * P⁻¹) v := by
  have hPu : IsUnit P := hP.1.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hE : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (t : ℝ),
      P⁻¹ * NormedSpace.exp ((t : ℂ) • (P * X * P⁻¹)) * P = NormedSpace.exp ((t : ℂ) • X) := by
    intro X t
    have e1 : ((t : ℂ) • (P * X * P⁻¹)) = P * ((t : ℂ) • X) * P⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.exp_conj P ((t : ℂ) • X) hPu]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
  have hconj : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (u : H),
      Formalism.MainNotions.S.dsig (k := k) (r := r) σ X u = dS (fun g => σ (P⁻¹ * g * P)) (P * X * P⁻¹) u := by
    intro X u
    unfold Formalism.MainNotions.S.dsig dS
    simp only [hE]
  induction w generalizing v with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v) =
      dS (fun g => σ (P⁻¹ * g * P)) (P * X * P⁻¹) (dSW (fun g => σ (P⁻¹ * g * P)) (w.map fun X => P * X * P⁻¹) v)
    rw [ih, hconj]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecSmOfDecBoundJ

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem decSm_of_decBoundJ {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (m N : ℕ)
    (hJ : DecBoundJ ε (fun g => σ (P⁻¹ * g * P)) m N) :
    ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, w.length ≤ N ∧ ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) ∧
      ∀ u ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g ^ m * ‖inner ℂ v (σ g u)‖ ≤
            C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w u‖).sum *
              (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v‖).sum := by
  obtain ⟨hinv, -, -, -⟩ := br_facts hP
  have hPPi : P * P⁻¹ = 1 := by
    rw [hinv]; exact (br_facts hP).2.1
  have hPiP : P⁻¹ * P = 1 := by
    rw [hinv]; exact (br_facts hP).2.2.1
  have hconj : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      P * (P⁻¹ * X * P) * P⁻¹ = X := by
    intro X
    calc P * (P⁻¹ * X * P) * P⁻¹ = (P * P⁻¹) * X * (P * P⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
  have hconj' : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hPiP, Matrix.one_mul, Matrix.mul_one]
  have hmapid : ∀ w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      ((w.map fun X => P⁻¹ * X * P).map fun X => P * X * P⁻¹) = w := by
    intro w
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w]
    exact List.map_congr_left (fun X _ => hconj X)
  obtain ⟨C, Ws, hWs, hb⟩ := hJ
  refine ⟨C, Ws.map fun w => w.map fun X => P⁻¹ * X * P, ?_, ?_⟩
  · intro w' hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
    refine ⟨by rw [List.length_map]; exact (hWs w hw).1, ?_⟩
    intro X' hX'
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hX'
    rw [bridge_lie hP, hconj]
    exact (hWs w hw).2 X hX
  · intro u hu v hv g hg
    have hsum : ∀ x : H,
        ((Ws.map fun w => w.map fun X => P⁻¹ * X * P).map
            fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w x‖).sum = nuJ (fun g => σ (P⁻¹ * g * P)) Ws x := by
      intro x
      unfold nuJ
      rw [List.map_map]
      congr 1
      refine List.map_congr_left (fun w _ => ?_)
      simp only [Function.comp_apply]
      rw [bridge_dsigW hP, hmapid]
    have key := hb u v ((bridge_smooth hP σ u).1 hu) ((bridge_smooth hP σ v).1 hv)
      (P * g * P⁻¹) ((bridge_group hP g).1 hg)
    simp only [] at key
    rw [hconj'] at key
    rw [hsum, hsum, bridge_gN hP]
    exact key

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end

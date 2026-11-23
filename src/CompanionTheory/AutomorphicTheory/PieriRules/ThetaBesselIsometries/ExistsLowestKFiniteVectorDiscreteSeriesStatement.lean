module

public import Formalism.RealPlaceAnalysis.StatementKT
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyExistsAndAny
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TorusWeightEigenAndRootShiftStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DominantRootSums
import Mathlib.Tactic.Lemma

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KStableFiniteDimSmoothCompactRootStable

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompactStable

open PI.UpqRep

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    {f : ℝ → H} {f' : H} (hf : HasDerivAt f f' 0) (hS : ∀ t, f t ∈ S) : f' ∈ S := by
  have h := hasDerivAt_iff_tendsto_slope.1 hf
  refine S.closed_of_finiteDimensional.mem_of_tendsto h (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact S.smul_of_tower_mem _ (S.sub_mem (hS t) (hS 0))

variable {k r : ℕ}

theorem dsig_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    {X : Mx k r} (hX : Xᴴ = -X) (hc : Hpk k r * X = X * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X v ∈ S := by
  have hL : InLieHpk k r X := by
    show Xᴴ * Hpk k r + Hpk k r * X = 0
    rw [hX, hc]; simp
  refine deriv_mem S (GlobalTheory.DerivedAction.hasDerivAt_dsig hL hsm) fun t => hS _ ⟨GlobalTheory.DerivedAction.exp_mem hL t, ?_⟩ v hv
  have h := CCRuleCW.exp_mem_UH 1 ((t : ℂ) • X) (by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hX]; simp)
  have h' : (NormedSpace.exp ((t : ℂ) • X))ᴴ * 1 * NormedSpace.exp ((t : ℂ) • X) = 1 := h
  rw [Matrix.mul_one] at h'
  exact Matrix.mem_unitaryGroup_iff'.2 h'

theorem dC_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1)
    {Y : Mx k r} (hc : Hpk k r * Y = Y * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    R.dC Y v ∈ S := by
  have hc' : Hpk k r * Yᴴ = Yᴴ * Hpk k r := by
    have := congrArg Matrix.conjTranspose hc
    rw [conjTranspose_mul, conjTranspose_mul, h1] at this
    exact this.symm
  have e : Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r = Yᴴ := by
    show Hpk k r * Yᴴ * Hpk k r = Yᴴ
    rw [hc', Matrix.mul_assoc, h2, Matrix.mul_one]
  unfold Rep.dC
  rw [e]
  refine S.add_mem (dsig_mem R S hS ?_ ?_ hv hsm) (S.smul_mem _ (dsig_mem R S hS ?_ ?_ hv hsm))
  · rw [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, conjTranspose_conjTranspose, ← smul_neg]
    congr 1
    · simp
    · abel
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, hc, hc']
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, conjTranspose_conjTranspose, ← neg_smul]
    congr 1
    · simp
    · abel
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, hc, hc']

theorem Jm_single {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    Jm ε * Matrix.single a b (1 : ℂ) = Matrix.single a b 1 * Jm ε := by
  ext i j
  unfold Jm
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hij
    simp [h]
  · simp [Matrix.single, hij]

theorem kStable_smooth_and_stable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → ∀ S : Submodule ℂ R.H, FiniteDimensional ℂ S → PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S → (∀ v ∈ S, R.KFin v ∧ v ∈ R.sm) ∧ ∀ a b, ε a = ε b → ∀ v ∈ S, R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v ∈ S := by
  intro hK k r ε mu R hR Q hQ S hfd hst
  have hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S := by
    intro g hg x hx
    obtain ⟨hk, hback⟩ := PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hQ hg
    have h := hst _ hk x hx
    simp only [hback] at h
    exact h
  have hA : ∀ v ∈ S, R.KFin v ∧ v ∈ R.sm := fun v hv =>
    ⟨⟨S, hfd, hv, hS⟩, hK k r ε mu R.H R.σ hR.1 hR.2 v ⟨S, hfd, hv, hS⟩⟩
  refine ⟨hA, fun a b hab v hv => ?_⟩
  have hsP : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.mp hQ.2
  have hPs : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hQ.2
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv hsP
  have hH : Qᴴ * Jm ε * Q = Hpk k r := hQ.1.2
  have hJ1 : (Jm ε)ᴴ = Jm ε := by
    unfold Jm
    rw [diagonal_conjTranspose]
    congr 1
    funext c
    by_cases hc : ε c = true <;> simp [hc]
  have hJ2 : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext c
    by_cases hc : ε c = true <;> simp [hc]
  have hm : ∀ A B : Mx k r, Qᴴ * A * Q * (Qᴴ * B * Q) = Qᴴ * (A * B) * Q := by
    intro A B
    calc Qᴴ * A * Q * (Qᴴ * B * Q) = Qᴴ * A * (Q * Qᴴ) * B * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (A * B) * Q := by rw [hPs, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine dC_mem R S hS ?_ ?_ ?_ hv (hA v hv).2
  · rw [← hH, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ1, Matrix.mul_assoc]
  · rw [← hH, hm, hJ2, Matrix.mul_one, hsP]
  · rw [← hH, hinv, hm, hm, Jm_single ε hab]

end GlobalTheory.CompactStable
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KStableFiniteDimSmoothCompactRootStableStatement

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.KStable_finiteDim_smooth_compactRoot_stable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → ∀ S : Submodule ℂ R.H, FiniteDimensional ℂ S → PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S → (∀ v ∈ S, R.KFin v ∧ v ∈ R.sm) ∧ ∀ a b, ε a = ε b → ∀ v ∈ S, R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v ∈ S := by
  first | exact @GlobalTheory.CompactStable.kStable_smooth_and_stable | exact GlobalTheory.CompactStable.kStable_smooth_and_stable | (intros; apply GlobalTheory.CompactStable.kStable_smooth_and_stable <;> assumption)
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeries

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowestVector

lemma lowK_eq {n : ℕ} (ε : Fin n → Bool) (mu : Fin n → ℝ) :
    PI.UpqRep.lowK ε mu = Formalism.QuantumDeterminants.lowK ε mu := rfl

theorem exists_lowest_vector : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ Formalism.REAL.KHighest ε E (Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (Formalism.REAL.kSpan ε E w) := by
  intro hK k r ε mu R hR Q E hQ hE
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hR Q hQ
  obtain ⟨-, -, -, -, -, ⟨S, hfin, hst, -, ⟨v, hvS, hv0, hvw⟩, hmax⟩, -⟩ := hD
  rw [lowK_eq] at hvw hmax
  obtain ⟨hS1, hS2⟩ := GlobalTheory.T.KStable_finiteDim_smooth_compactRoot_stable hK k r ε mu R hR Q hQ S hfin hst
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  set u : R.H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hu
  have huS : u ∈ S := S.smul_mem _ hvS
  have huw : PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (Formalism.QuantumDeterminants.lowK ε mu) u := by
    intro θ hθ
    have := hvw θ hθ
    simp only at this ⊢
    rw [hu, map_smul, this, smul_comm]
  let w : R.smSub := ⟨u, (hS1 u huS).2⟩
  obtain ⟨hw1, hw2⟩ := GlobalTheory.T.torusWeight_eigen_and_rootShift hK k r ε mu R hR Q E hQ hE (Formalism.QuantumDeterminants.lowK ε mu) w huw
  refine ⟨w, ?_, (hS1 u huS).1, ⟨hw1, ?_⟩, ?_⟩
  · show ‖u‖ = 1
    rw [hu, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · intro a b hab he
    by_contra h0
    have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
      rw [hE a b w]; exact hS2 a b he u huS
    have h0' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact GlobalTheory.DominantRootSums.not_cDom_add_root _ ε _ a b hab (hmax _ _ hmem h0' (hw2 a b))
  · have hle : Formalism.REAL.kSpan ε E w ≤ S.comap R.smSub.subtype := by
      refine sInf_le ⟨huS, ?_⟩
      intro a b he x hx
      show ((E a b x : R.smSub) : R.H) ∈ S
      rw [hE a b x]; exact hS2 a b he _ hx
    have : FiniteDimensional ℂ (S.comap R.smSub.subtype) :=
      FiniteDimensional.of_injective
        ((R.smSub.subtype.comp (S.comap R.smSub.subtype).subtype).codRestrict S (fun x => x.2))
        (fun x y h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.LowestVector
end
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeriesStatement

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ Formalism.REAL.KHighest ε E (Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (Formalism.REAL.kSpan ε E w) := by
  first | exact @GlobalTheory.LowestVector.exists_lowest_vector | exact GlobalTheory.LowestVector.exists_lowest_vector | (intros; apply GlobalTheory.LowestVector.exists_lowest_vector <;> assumption)
end Gp91
end
end

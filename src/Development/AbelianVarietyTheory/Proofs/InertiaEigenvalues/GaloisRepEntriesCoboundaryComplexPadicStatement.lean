module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexFixedElementApproximation
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixMulEntryNormLeUltrametricStatement
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Data.Nat.Choose.Multinomial

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexMatrixGaloisSubgroupApproxima

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.AxLemma

theorem ax_lemma_matrix : ∀ (l : ℕ) [Fact l.Prime] , ∃ c : ℝ, 0 < c ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (H : Subgroup ↥(GK K)) (Y : Matrix n n ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ∀ i j, ‖(Y.map (Formalism.Per.σC (g : GQ l)) - Y) i j‖ ≤ r) → ∃ Z : Matrix n n ℂ_[l], (∀ g ∈ H, Z.map (Formalism.Per.σC (g : GQ l)) = Z) ∧ ∀ i j, ‖(Y - Z) i j‖ ≤ c * r := by
  intro l _
  obtain ⟨c, hc, hax⟩ := ax_lemma_complete l
  refine ⟨c, hc, fun n _ _ K H Y r hr hY => ?_⟩
  have hent : ∀ i j, ∃ z : Om l, (∀ g ∈ H.map (GK K).subtype, g z = z) ∧
      ‖Y i j - (z : ℂ_[l])‖ ≤ c * r := by
    intro i j
    refine hax (H.map (GK K).subtype) (Y i j) r hr ?_
    rintro g' ⟨g, hg, rfl⟩
    have := hY g hg i j
    simpa [Matrix.sub_apply, Matrix.map_apply] using this
  choose z hz hzY using hent
  refine ⟨Matrix.of fun i j => (z i j : ℂ_[l]), ?_, ?_⟩
  · intro g hg
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [GlobalTheory.RingBasics.σC_coe]
    congr 1
    exact hz i j _ ⟨g, hg, rfl⟩
  · intro i j
    simpa [Matrix.sub_apply, Matrix.of_apply] using hzY i j

end GlobalTheory.AxLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexMatrixGaloisSubgroupApproximaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.axLemma_padicComplexMatrix_galoisSubgroup_approximation : ∀ (l : ℕ) [Fact l.Prime] , ∃ c : ℝ, 0 < c ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (H : Subgroup ↥(GK K)) (Y : Matrix n n ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ∀ i j, ‖(Y.map (Formalism.Per.σC (g : GQ l)) - Y) i j‖ ≤ r) → ∃ Z : Matrix n n ℂ_[l], (∀ g ∈ H, Z.map (Formalism.Per.σC (g : GQ l)) = Z) ∧ ∀ i j, ‖(Y - Z) i j‖ ≤ c * r := by
  first | exact @GlobalTheory.AxLemma.ax_lemma_matrix | exact GlobalTheory.AxLemma.ax_lemma_matrix | (intros; apply GlobalTheory.AxLemma.ax_lemma_matrix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisInvComplexPadicPeriodMatrix

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem GlobalTheory.PMon.galois_inv_period_matrix : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∀ g : ↥(GK K), ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) * (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) := by
  intro l _ n _ _ K ρ M h g
  set σ := Formalism.Per.σC (g : GQ l) with hσ
  have h1 : (M : Matrix n n ℂ_[l]).map σ * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h2 := h g
  set R := (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l])
  have h3 : R = (M : Matrix n n ℂ_[l]) * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ := by
    calc R = R * ((M : Matrix n n ℂ_[l]).map σ * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h2]
  rw [h3, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisInvComplexPadicPeriodMatrixStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_inv_complexPadic_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∀ g : ↥(GK K), ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) * (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) := by
  first | exact @GlobalTheory.PMon.galois_inv_period_matrix | exact GlobalTheory.PMon.galois_inv_period_matrix | (intros; apply GlobalTheory.PMon.galois_inv_period_matrix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalisedPeriodAlgebraicEstimate

section

@[expose] public section

namespace GlobalTheory

theorem normalisedPeriod_algebraic_estimate :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t →
      (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z →
      (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) →
      ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by
  intro E _ _ n _ _ σ r M Mi Z a s t ha hs ht hσ hMMi hr hZ hM hD hrt i j
  set D := Mi - Z with hDdef
  set C := M * Z with hCdef
  have hC1 : C = 1 - M * D := by
    rw [hCdef, hDdef, Matrix.mul_sub, hMMi]; abel
  have hCσ : C.map σ = M.map σ * Z := by
    rw [hCdef, Matrix.map_mul, hZ]
  have hrC : r * C.map σ = C := by rw [hCσ, ← Matrix.mul_assoc, hr]
  have hX : C.map σ - 1 = -((M * D).map σ) := by
    rw [hC1, Matrix.map_sub σ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]; abel
  have hkey : σ (-C i j) - (-C i j) - (r - 1) i j = ((r - 1) * (C.map σ - 1)) i j := by
    have h2 : ((r - 1) * (C.map σ - 1)) = C - C.map σ - (r - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hrC, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul]; abel
    rw [h2]
    simp [Matrix.sub_apply, Matrix.map_apply, map_neg]
    ring
  have hMD : ∀ i j, ‖(M * D) i j‖ ≤ a * s :=
    GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n M D a s ha hs hM hD
  have hXb : ∀ i j, ‖(C.map σ - 1) i j‖ ≤ a * s := by
    intro i j
    rw [hX, Matrix.neg_apply, norm_neg, Matrix.map_apply, hσ]
    exact hMD i j
  rw [hkey]
  exact GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (r - 1) (C.map σ - 1) t (a * s) ht (mul_nonneg ha hs) hrt hXb i j

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalisedPeriodAlgebraicEstimateStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.norm_apply_neg_mul_sub_sub_le_mul : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t → (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z → (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) → ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by
  first | exact @GlobalTheory.normalisedPeriod_algebraic_estimate | exact GlobalTheory.normalisedPeriod_algebraic_estimate | (intros; apply GlobalTheory.normalisedPeriod_algebraic_estimate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesCoboundaryComplexPadic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem ph_c_cob : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∃ b : ℝ, 0 < b ∧ ∀ (H : Subgroup ↥(GK K)) (t : ℝ), 0 < t → (∀ g ∈ H, ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ t) → ∀ i j, ∃ y : ℂ_[l], ∀ g ∈ H, ‖Formalism.Per.σC (g : GQ l) y - y - algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j)‖ ≤ b * t ^ 2 := by
  intro l _ n _ _ K ρ M hM
  set Mi : Matrix n n ℂ_[l] := ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) with hMi
  set a : ℝ := 1 + ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) with ha
  have hterm : ∀ i j, ‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖ ≤ ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) := by
    intro i j
    calc ‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖ ≤ ∑ j', (‖(M : Matrix n n ℂ_[l]) i j'‖ + ‖Mi i j'‖) :=
          Finset.single_le_sum (f := fun j' => ‖(M : Matrix n n ℂ_[l]) i j'‖ + ‖Mi i j'‖)
            (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖(M : Matrix n n ℂ_[l]) i' j'‖ + ‖Mi i' j'‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖(M : Matrix n n ℂ_[l]) i' j'‖ + ‖Mi i' j'‖))
            (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ i)
  have hMa : ∀ i j, ‖(M : Matrix n n ℂ_[l]) i j‖ ≤ a := by
    intro i j; have := hterm i j; have := norm_nonneg (Mi i j); rw [ha]; linarith
  have hMia : ∀ i j, ‖Mi i j‖ ≤ a := by
    intro i j; have := hterm i j; have := norm_nonneg ((M : Matrix n n ℂ_[l]) i j); rw [ha]; linarith
  have ha0 : 0 < a := by
    rw [ha]; have : 0 ≤ ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
    linarith
  obtain ⟨c, hc, hAx⟩ := GlobalTheory.T.axLemma_padicComplexMatrix_galoisSubgroup_approximation l
  refine ⟨c * a ^ 2, by positivity, ?_⟩
  intro H t ht hρ i j
  set rC : ↥(GK K) → Matrix n n ℂ_[l] := fun g => (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) with hrCdef
  have hrent : ∀ g : ↥(GK K), ∀ i j, (rC g - 1) i j = algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j) := by
    intro g i j
    have e : rC g - 1 = (algebraMap ℚ_[l] ℂ_[l]).mapMatrix ((ρ g : Matrix n n ℚ_[l]) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e]; rfl
  have hrow : ∀ g ∈ H, ∀ i j, ‖(rC g - 1) i j‖ ≤ t := by
    intro g hg i j; rw [hrent, norm_algebraMap']; exact hρ g hg i j
  have hY : ∀ g ∈ H, ∀ i j, ‖(Mi.map (Formalism.Per.σC (g : GQ l)) - Mi) i j‖ ≤ a * t := by
    intro g hg i j
    have hs := GlobalTheory.T.galois_inv_complexPadic_periodMatrix l n K ρ M hM g
    have e : Mi.map (Formalism.Per.σC (g : GQ l)) - Mi = Mi * (rC g - 1) := by
      rw [hMi, hs, mul_sub, mul_one]
    rw [e]
    exact GlobalTheory.T.norm_mul_apply_le_of_ultrametric ℂ_[l] n Mi (rC g - 1) a t ha0.le ht.le hMia (hrow g hg) i j
  obtain ⟨Z, hZ, hZb⟩ := hAx n K H Mi (a * t) (by positivity) hY
  refine ⟨-((M : Matrix n n ℂ_[l]) * Z) i j, fun g hg => ?_⟩
  have hcore := GlobalTheory.T.norm_apply_neg_mul_sub_sub_le_mul ℂ_[l] n (Formalism.Per.σC (g : GQ l)) (rC g) (M : Matrix n n ℂ_[l]) Mi Z a (c * (a * t)) t
    ha0.le (by positivity) ht.le (GlobalTheory.RingBasics.norm_σC _) (by rw [hMi]; exact M.mul_inv) (hM g) (hZ g hg) hMa hZb (hrow g hg) i j
  rw [hrent] at hcore
  calc _ ≤ t * (a * (c * (a * t))) := hcore
    _ = c * a ^ 2 * t ^ 2 := by ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesCoboundaryComplexPadicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisRep_entries_coboundary_complexPadic : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∃ b : ℝ, 0 < b ∧ ∀ (H : Subgroup ↥(GK K)) (t : ℝ), 0 < t → (∀ g ∈ H, ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ t) → ∀ i j, ∃ y : ℂ_[l], ∀ g ∈ H, ‖Formalism.Per.σC (g : GQ l) y - y - algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j)‖ ≤ b * t ^ 2 := by
  first | exact @GlobalTheory.ph_c_cob | exact GlobalTheory.ph_c_cob | (intros; apply GlobalTheory.ph_c_cob <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokerFiniteLengthOfPrimitiveDivisorStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelTorsionFreeOfBoundedLeftInverseStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemLeftDivisorSetPhiModuleHomStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusResidueSliceMemBoundedLeftDivisorSetStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMemOfFrobeniusLinkedBoundedSeriesIdealsStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEPowMulFrobMemRightDivisorSet

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def boundedCoeffSeries (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] : Subalgebra O K⟦X⟧ where
  carrier := {f | ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c}
  mul_mem' hf hg := Hom.bdd_mul hf hg
  add_mem' hf hg := Hom.bdd_add hf hg
  algebraMap_mem' c := ⟨1, (A O K).algebraMap_mem c⟩

theorem Hom.exists_E_pow_mul_frob_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.rdivSet τ := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have key : ∀ {μ : Type} [Fintype μ] (Y : ZMod a → Matrix μ μ K⟦X⟧),
      (∀ τ i j, Y τ i j ∈ invE l e (A O K)) → ∃ n : ℕ, ∀ τ i j, E K l e ^ n * Y τ i j ∈ A O K := by
    intro μ _ Y hY
    choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
    refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (hn (τ, i, j))
  obtain ⟨n₁, hn₁⟩ := key P.mx P.mx_mem
  obtain ⟨n₂, hn₂⟩ := key Q.mxInv Q.mxInv_mem
  refine ⟨n₁ + n₂, fun τ h hh => ?_⟩
  obtain ⟨hb, Y, ⟨c, hc⟩, hF⟩ := hh
  have hA : ∀ f ∈ A O K, f ∈ boundedCoeffSeries O K := fun f hf => ⟨1, hf⟩
  have hfr : ∀ f ∈ boundedCoeffSeries O K, frob K l f ∈ boundedCoeffSeries O K := by
    rintro f ⟨d, hd⟩
    refine ⟨d, fun n => ?_⟩
    rw [coeff_frob]
    split_ifs
    · exact hd _
    · simpa using (norm_nonneg _).trans (hd 0)
  have hE : E K l e ∈ A O K := E_mem l e _
  refine ⟨mul_mem (hA _ (pow_mem hE _)) (hfr _ hb),
    (E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ), ?_, ?_⟩
  · have hmem : ∀ i j, ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ)) i j ∈
        boundedCoeffSeries O K := by
      intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact sum_mem fun k _ => mul_mem (sum_mem fun m _ =>
        mul_mem (hA _ (hn₁ τ i m)) (hfr _ ⟨c, fun n => hc m k n⟩)) (hA _ (hn₂ τ k j))
    choose d hd using hmem
    obtain ⟨D, hD⟩ := Finite.exists_le (fun p : ι × κ => d p.1 p.2)
    exact ⟨D, fun i j n => (hd i j n).trans (hD (i, j))⟩
  · have hmap : (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) =
        frob K l h • (1 : Matrix κ κ K⟦X⟧) := by
      have h1 : (F.mat (τ - 1) * Y).map (frob K l) = (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) :=
        Matrix.map_mul (f := (frob K l).toRingHom)
      rw [← h1, hF]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    calc F.mat τ * ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ))
        = (E K l e ^ n₁ * E K l e ^ n₂) • ((F.mat τ * P.mx τ) * Y.map (frob K l) * Q.mxInv τ) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = (E K l e ^ n₁ * E K l e ^ n₂) •
          (Q.mx τ * ((F.mat (τ - 1)).map (frob K l) * Y.map (frob K l)) * Q.mxInv τ) := by
          rw [F.comm, Matrix.mul_assoc (Q.mx τ)]
      _ = (E K l e ^ (n₁ + n₂) * frob K l h) • (1 : Matrix κ κ K⟦X⟧) := by
          rw [hmap, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mx_mul_mxInv, smul_smul, pow_add]

end GlobalTheory.BK
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEPowMulFrobMemRightDivisorSetStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_E_pow_mul_frob_mem_rightDivisorSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.rdivSet τ := by
  first | exact @GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet | exact GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet | (intros; apply GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSliceMemRightDivisorSet

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.RdivSlice

theorem frobSlice_frob_mul {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] {i : ℕ} (hi : i < l)
    (f z : K⟦X⟧) : frobSlice l i (frob K l f * z) = f * frobSlice l i z := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  symm
  refine Finset.sum_of_injOn (fun p : ℕ × ℕ => (l * p.1, l * p.2 + i)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ - ⟨p', q'⟩ - h
    simp only [Prod.mk.injEq, add_left_inj] at h ⊢
    exact ⟨Nat.eq_of_mul_eq_mul_left hl h.1, Nat.eq_of_mul_eq_mul_left hl h.2⟩
  · rintro ⟨p, q⟩ h
    simp only [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    rw [← h]; ring
  · rintro ⟨p, q⟩ h hn
    rw [coeff_frob]
    split_ifs with hd
    · exfalso
      obtain ⟨t, rfl⟩ := hd
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at h
      have ht : t ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * t := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      refine hn ⟨(t, s), by simp, ?_⟩
      rw [mul_add] at h
      simp only [Prod.mk.injEq, true_and]
      omega
    · simp
  · rintro ⟨p, q⟩ -
    simp only [coeff_frob, coeff_frobSlice, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hl]

theorem frobSlice_sum {K : Type} [Field K] (l i : ℕ) {μ : Type} (s : Finset μ) (f : μ → K⟦X⟧) :
    frobSlice l i (∑ j ∈ s, f j) = ∑ j ∈ s, frobSlice l i (f j) := by
  ext n

  simp only [coeff_frobSlice, map_sum]

theorem bdd_matrix_mul {K : Type} [NormedField K] [IsUltrametricDist K] {μ ν ρ : Type} [Fintype ν]
    {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧} (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c)
    (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩

  rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun m => by rw [mul_one]; exact (ha i k m).trans (le_max_left _ _))
    (fun m => by rw [mul_one]; exact (hb k j m).trans (le_max_left _ _)) n

theorem exists_pow_smul_bdd {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [NeZero a] {μ : Type} [Fintype μ]
    (Y : ZMod a → Matrix μ μ K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) :
    ∃ N : ℕ, ∀ τ i j n, ‖coeff n ((E K l e ^ N • Y τ) i j)‖ ≤ 1 := by
  choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
  refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
  rw [Matrix.smul_apply, smul_eq_mul, hc, pow_add, mul_assoc]
  exact mem_A.1 (mul_mem (pow_mem (E_mem l e (A O K)) c) (hn (τ, i, j)))

theorem exists_frobSlice_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.rdivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨α, hα⟩ := exists_pow_smul_bdd P.mxInv P.mxInv_mem
  obtain ⟨β, hβ⟩ := exists_pow_smul_bdd Q.mx Q.mx_mem
  refine ⟨α + β, fun τ h hh i hi => ?_⟩
  obtain ⟨hb, Y, hY, hFY⟩ := hh
  obtain ⟨c, hc⟩ := GlobalTheory.BK.Hom.bdd_mul (f := E K l e ^ (α + β))
    ⟨1, mem_A.1 (pow_mem (E_mem l e (A O K)) _)⟩ hb
  obtain ⟨d, hd⟩ := bdd_matrix_mul (bdd_matrix_mul ⟨1, hα τ⟩ hY) ⟨1, hβ τ⟩
  have h1 : (F.mat (τ - 1)).map (frob K l) * P.mxInv τ = Q.mxInv τ * F.mat τ := by
    calc _ = Q.mxInv τ * (Q.mx τ * (F.mat (τ - 1)).map (frob K l)) * P.mxInv τ := by
          rw [← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]
      _ = _ := by
          rw [← F.comm, Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
  have h2 : (F.mat (τ - 1)).map (frob K l) *
      ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)) =
      (E K l e ^ (α + β) * h) • (1 : Matrix κ κ K⟦X⟧) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (Q.mxInv τ), hFY,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mxInv_mul_mx, smul_smul, smul_smul,
      pow_add]
  refine ⟨⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩,
    ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)).map (frobSlice l i),
    ⟨d, fun s t n => by rw [Matrix.map_apply, coeff_frobSlice]; exact hd _ _ _⟩, ?_⟩
  ext1 s t
  have h3 := congrArg (fun M : Matrix κ κ K⟦X⟧ => frobSlice l i (M s t)) h2
  simp only [Matrix.mul_apply (M := (F.mat (τ - 1)).map (frob K l)), frobSlice_sum,
    Matrix.map_apply, frobSlice_frob_mul l hi] at h3
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [h3, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · simp
  · ext n
    simp [coeff_frobSlice]

end GlobalTheory.BK.RdivSlice
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSliceMemRightDivisorSetStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_frobeniusSlice_mem_rightDivisorSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.rdivSet (τ - 1) := by
  first | exact @GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet | exact GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet | (intros; apply GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthCokerOfSurjectiveModUniformizer

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BK.Hom.finiteLength_coker_of_generic : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := (map_natCast _ _).symm
  have hlK : ‖(l : K)‖ < 1 := by
    rw [h1, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl2)
  have hl0 : (l : K) ≠ 0 := by
    rw [h1]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hone : ∃ c : ℝ, ∀ n, ‖coeff n (1 : K⟦X⟧)‖ ≤ c :=
    ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  refine ⟨fun hyp => GlobalTheory.T.coker_finite_length_of_primitive_divisor O K l e a ι κ P Q F hyp ?_, fun hyp => GlobalTheory.T.cokernel_torsionFree_of_bounded_leftInverse O K l e a ι κ P Q F hyp ?_⟩
  · rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun _ j => isEmptyElim j⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.exists_E_pow_mul_frob_mem_rightDivisorSet O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.exists_frobeniusSlice_mem_rightDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.rdivSet (fun τ x hx y hy => Hom.rdivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.rdivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (F.mat τ * Y) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (F.mem τ i0 j) (hY j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun i _ => isEmptyElim i⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.frob_mem_leftDivisorSet_phiModuleHom O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.frobeniusResidueSlice_mem_boundedLeftDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.ldivSet (fun τ x hx y hy => Hom.ldivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.ldivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (Y * F.mat τ) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY i0 j) (F.mem τ j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthCokerOfSurjectiveModUniformizerStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  first | exact @GlobalTheory.BK.Hom.finiteLength_coker_of_generic | exact GlobalTheory.BK.Hom.finiteLength_coker_of_generic | (intros; apply GlobalTheory.BK.Hom.finiteLength_coker_of_generic <;> assumption)
end
end

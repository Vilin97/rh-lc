module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Formalism.RealPlaceAnalysis.StatementU
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtension
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeGeneratedByHighest
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqrtNsqLeOfAbsLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
import Mathlib.MeasureTheory.Function.L2Space
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumNormSqOfIsometry

section

@[expose] public section

open Formalism.REAL Matrix

namespace GlobalTheory.OnbSum

theorem conjTranspose_eq_of_inG {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : inG ε X) : Xᴴ = -(Jm ε * X * Jm ε) := by
  have h' : Xᴴ * Jm ε + Jm ε * X = 0 := h
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h'
  calc Xᴴ = Xᴴ * (Jm ε * Jm ε) := by rw [Jm_mul_self, Matrix.mul_one]
    _ = Xᴴ * Jm ε * Jm ε := (Matrix.mul_assoc _ _ _).symm
    _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]

theorem trace_im_eq_zero {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : (Matrix.trace (A * Bᴴ)).im = 0 := by
  have hA' := conjTranspose_eq_of_inG hA
  have hB' := conjTranspose_eq_of_inG hB
  have swap : Matrix.trace (B * Aᴴ) = Matrix.trace (A * Bᴴ) := by
    rw [hA', hB', Matrix.mul_neg, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_neg, neg_inj]
    calc Matrix.trace (B * (Jm ε * A * Jm ε)) = Matrix.trace ((B * Jm ε * A) * Jm ε) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Jm ε * (B * Jm ε * A)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Jm ε * B * Jm ε) * A) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (A * (Jm ε * B * Jm ε)) := Matrix.trace_mul_comm _ _
  have hstar : (starRingEnd ℂ) (Matrix.trace (A * Bᴴ)) = Matrix.trace (A * Bᴴ) := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, swap]
  exact Complex.conj_eq_iff_im.mp hstar

theorem sum_norm_sq_of_isometry {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Matrix ι κ ℂ) (hM : Mᴴ * M = 1)
    (y : κ → V) : ∑ i, ‖∑ p, M i p • y p‖ ^ 2 = ∑ p, ‖y p‖ ^ 2 := by
  have key : ∀ p q, ∑ i, (starRingEnd ℂ) (M i p) * M i q = if p = q then (1 : ℂ) else 0 := by
    intro p q
    have h := congrFun (congrFun hM p) q
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa only [Matrix.conjTranspose_apply, Complex.star_def] using h
  have hsq : ∀ v : V, (‖v‖ : ℂ) ^ 2 = inner ℂ v v := fun v => (inner_self_eq_norm_sq_to_K v).symm
  have expand : ∀ i, inner ℂ (∑ p, M i p • y p) (∑ q, M i q • y q) =
      ∑ p, ∑ q, (starRingEnd ℂ) (M i p) * M i q * inner ℂ (y p) (y q) := by
    intro i
    rw [sum_inner]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [inner_smul_left, inner_smul_right, mul_assoc]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [hsq, expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, key]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem onb_sum : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (y : Fin n → Fin n → V), (∀ F : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsONFamily ε F → ∑ i, ‖∑ a, ∑ b, F i a b • y a b‖ ^ 2 = ∑ a, ∑ b, ‖y a b‖ ^ 2) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖∑ a, ∑ b, X a b • y a b‖ ^ 2 ≤ hs X * ∑ a, ∑ b, ‖y a b‖ ^ 2 := by
  intro n ε V _ _ y
  refine ⟨fun F hF => ?_, fun X => ?_⟩
  · let M : Matrix (Fin (n ^ 2)) (Fin n × Fin n) ℂ := fun i p => F i p.1 p.2
    have hrow : M * Mᴴ = 1 := by
      ext i j
      have hre := hF.2 i j
      have him := trace_im_eq_zero (hF.1 i) (hF.1 j)
      have htr : Matrix.trace (F i * (F j)ᴴ) = (M * Mᴴ) i j := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
        rw [Fintype.sum_prod_type]
      rw [← htr, Matrix.one_apply]
      apply Complex.ext
      · rw [hre]; split_ifs <;> simp
      · rw [him]; split_ifs <;> simp
    have e : Fin n × Fin n ≃ Fin (n ^ 2) := Fintype.equivOfCardEq (by simp [sq])
    have hcol : Mᴴ * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mp hrow
    have hiso := sum_norm_sq_of_isometry M hcol (fun p => y p.1 p.2)
    simpa only [M, Fintype.sum_prod_type] using hiso
  · have h1 : ‖∑ a, ∑ b, X a b • y a b‖ ≤ ∑ a, ∑ b, ‖X a b‖ * ‖y a b‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_smul (X a b) (y a b)).le))
    have h2 : (∑ a, ∑ b, ‖X a b‖ * ‖y a b‖) ^ 2 ≤ hs X * ∑ a, ∑ b, ‖y a b‖ ^ 2 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
        (fun p => ‖X p.1 p.2‖) (fun p => ‖y p.1 p.2‖)
      simpa only [hs, Fintype.sum_prod_type] using hcs
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

end GlobalTheory.OnbSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOfMemLowKSub

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepBoundOneRep

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem stepConst_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ stepConst n b P := by
  have h1 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (sq_nonneg b)
  have h2 : 0 ≤ 3 / 2 * (n : ℝ) ^ (3 / 2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have h3 : 0 ≤ 3 * (P : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg P)
  simp only [stepConst]
  linarith

theorem stepSpace_le {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Vs : Submodule ℂ H)
    (E : Fin n → Fin n → Module.End ℂ Vs) (hE : GlRel E)
    (hd : ∀ X, inG ε X → ∀ u : Vs, HasDerivAt (orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0)
    (u : Vs) (hu : (kSpan ε E u).map Vs.subtype = lowKSub ε lam σ) (P : ℕ) :
    stepSpace ε lam σ P ≤ (pfil ε E u P).map Vs.subtype := by
  have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, inG ε X) → ∀ w ∈ lowKSub ε lam σ,
      ∃ x : Vs, x ∈ pfil ε E u l.length ∧ (x : H) = dWord σ l w := by
    intro l
    induction l with
    | nil =>
      intro _ w hw
      rw [← hu] at hw
      obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.mp hw
      refine ⟨x, ?_, ?_⟩
      · rw [List.length_nil, poincare_filtration_zero]
        exact hx
      · exact hxw
    | cons X l ih =>
      intro hl w hw
      obtain ⟨x, hx, hxe⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) w hw
      refine ⟨∑ a, ∑ b, X a b • E a b x, ?_, ?_⟩
      · exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
          Submodule.smul_mem _ _ (poincare_filtration_succ ε E u hE _ a b x hx)
      · change _ = dAct σ X (dWord σ l w)
        rw [← hxe, dAct, (hd X (hl X List.mem_cons_self) x).deriv]
  rw [stepSpace, Submodule.span_le]
  rintro v ⟨l, w, hl, hX, hw, rfl⟩
  obtain ⟨x, hx, hxe⟩ := key l hX w hw
  exact Submodule.mem_map.mpr ⟨x, pfil_monotone_in_length ε E u hl hx, hxe⟩

theorem smooth_of_mem_lowKSub {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hU : IsURepOn (UJset ε) σ)
    (hS : IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ)) (v : H) (hv : v ∈ lowKSub ε lam σ) :
    SmoothOnGV ε (fun g => σ g v) := by
  obtain ⟨α, hα, hαc, hfix⟩ := exists_smooth_fix_lowKSub n ε lam H σ hU hS
  have hcu : Continuous (fun g : UJ ε => umat g) := Units.continuous_val.comp continuous_subtype_val
  have hcα : Continuous (fun g : UJ ε => α (umat g)) := by
    refine continuous_iff_continuousAt.mpr fun g₀ => ?_
    obtain ⟨U, F, hUo, hgU, hF, hFα⟩ := hα (umat g₀) g₀.2
    have hev : (fun g : UJ ε => F (umat g)) =ᶠ[nhds g₀] (fun g : UJ ε => α (umat g)) := by
      filter_upwards [hcu.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgU)] with g hg
      exact (hFα _ hg g.2).symm
    exact ((hF.continuousOn.continuousAt (hUo.mem_nhds hgU)).comp hcu.continuousAt).congr hev
  have hcσ : Continuous (fun g : UJ ε => σ (umat g) v) :=
    (hU.2.2 v).comp_continuous hcu fun g => g.2
  have hint : Integrable (fun g : UJ ε => α (umat g) • σ (umat g) v) (muG ε) :=
    (hcα.smul hcσ).integrable_of_hasCompactSupport (hαc.smul_right)
  have hv : v = ∫ g : UJ ε, α (umat g) • σ (umat g) v ∂(muG ε) := by
    refine ext_inner_left ℂ fun y => ?_
    rw [← integral_inner hint y, ← hfix v hv y]
    simp only [inner_smul_right]
  have hsm := GlobalTheory.GardingSmooth.garding_smooth n ε H σ hU α hα hαc v
  rw [← hv] at hsm
  exact hsm

theorem stepBound_of_eigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (b : ℝ), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → (∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ)) → (∀ a, |lam a| ≤ b ^ 2) → (∀ P : ℕ, FiniteDimensional ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec ε σ w) ∧ (∀ F : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsONFamily ε F → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ (F i) w‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖w‖ ^ 2) ∧ ∀ X, Formalism.REAL.inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w‖ ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖w‖) := by
  intro n ε H _ _ _ σ lam b hU hS heig hb
  obtain ⟨Vs, E, hVs, hGl, hUn, hD, hEq⟩ := SmoothVecMod.smoothVec_unitary_module n ε H σ hU
  have hlow : lowKSub ε lam σ ≤ Vs := fun v hv =>
    (hVs v).mpr (smooth_of_mem_lowKSub ε lam σ hU hS v hv)
  obtain ⟨u, -, hKu, hmap, hfd⟩ := GlobalTheory.KTypeHighest.kType_generated_by_highest n ε H σ Vs E hU
    ⟨hVs, hGl, hUn, hD, hEq⟩ _ (lowKSub ε lam σ) hS hlow
  have huS : (u : H) ∈ lowKSub ε lam σ := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (mem_kSpan_self' ε E u)
  have hCas := GlobalTheory.CasimirEigen.cas_eq_of_isZEigen n ε H σ Vs E lam hU ⟨hVs, hGl, hUn, hD, hEq⟩ u
    (heig _ huS)
  have hKind : KindA ε E lam u := ⟨hKu, hCas, hfd⟩
  have hAlg := GlobalTheory.algebraic_step_bound Vs n ε E lam u b hGl hUn hKind hb
  have hC : ∀ P : ℕ, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P := fun P => stepConst_nonneg n b P
  have hmem : ∀ (P : ℕ) (w : H), w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P →
      ∃ x : Vs, x ∈ pfil ε E u P ∧ (x : H) = w := fun P w hw =>
    Submodule.mem_map.mp (stepSpace_le ε lam σ Vs E hGl (fun X hX x => hD X hX x) u hmap P hw)
  have hact : ∀ X, inG ε X → ∀ x : Vs,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H) = ((∑ a, ∑ c, X a c • E a c x : Vs) : H) := fun X hX x => by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct, (hD X hX x).deriv]
  have hbound : ∀ P : ℕ, ∀ x ∈ pfil ε E u P,
      ∑ a, ∑ c, ‖E a c x‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2 := hAlg
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : FiniteDimensional ℂ (pfil ε E u P) := pfil_finite_dimensional ε E u hfd P
    exact Submodule.finiteDimensional_of_le
      (stepSpace_le ε lam σ Vs E hGl (fun X hX x => hD X hX x) u hmap P)
  · intro w hw
    obtain ⟨x, -, rfl⟩ := hmem P w hw
    exact fun X hX => (hD X hX x).differentiableAt
  · intro F hF w hw
    obtain ⟨x, hx, rfl⟩ := hmem P w hw
    have hON := (GlobalTheory.OnbSum.onb_sum n ε Vs (fun a c => E a c x)).1 F hF
    calc ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ (F i) (x : H)‖ ^ 2
        = ∑ i, ‖∑ a, ∑ c, F i a c • E a c x‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hact (F i) (hF.1 i) x]
          rfl
      _ = ∑ a, ∑ c, ‖E a c x‖ ^ 2 := hON
      _ ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2 := hbound P x hx
      _ = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖(x : H)‖ ^ 2 := rfl
  · intro X hX w hw
    obtain ⟨x, hx, rfl⟩ := hmem P w hw
    have hsq := (GlobalTheory.OnbSum.onb_sum n ε Vs (fun a c => E a c x)).2 X
    have hhs : 0 ≤ Formalism.REAL.hs X := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hnorm : ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H)‖ = ‖∑ a, ∑ c, X a c • E a c x‖ := by
      rw [hact X hX x]
      rfl
    have h2 : ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H)‖ ^ 2 ≤
        (Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖(x : H)‖) ^ 2 := by
      rw [hnorm, mul_pow, mul_pow, Real.sq_sqrt hhs]
      calc ‖∑ a, ∑ c, X a c • E a c x‖ ^ 2 ≤ Formalism.REAL.hs X * ∑ a, ∑ c, ‖E a c x‖ ^ 2 := hsq
        _ ≤ Formalism.REAL.hs X * (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hbound P x hx) hhs
        _ = Formalism.REAL.hs X * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖(x : H)‖ ^ 2 := by
          rw [mul_assoc]
          rfl
    have hr : 0 ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖(x : H)‖ :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hC P)) (norm_nonneg _)
    nlinarith [norm_nonneg (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H))]

end GlobalTheory.StepBoundOneRep
end
end

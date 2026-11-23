module

public import Formalism.RealPlaceAnalysis.StatementC
public import Formalism.RealPlaceAnalysis.StatementKT
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ChainBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContDiffFderivMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsDer
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsDerLowKSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Algebra.Group.Units
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KHighestEqSmulOfMinusKilled
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLowKOfLeLowKSub

section

@[expose] public section

open Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.LowHW

theorem height_root {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * Formalism.REAL.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem height_sum {n : ℕ} (c : Fin n → Fin n → ℕ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) i
      = ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
  simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem cdom_antisymm {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h1 : CDom ε μ Λ) (h2 : CDom ε Λ μ) :
    μ = Λ := by
  apply Formalism.MainNotions.BridgeLemma.cdom_antisymm <;> assumption

end GlobalTheory.LowHW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGardingKMap

section

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.SmoothKType


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem exists_garding_kMap (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (hσ : IsURepOn (UJset ε) σ) (hK : IsKTypeOf ε σ μ S) :
    ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (T : S →ₗ[ℂ] H), SmoothOnG ε α ∧
      HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
      (∀ (s : S) (u : H), ⟪u, T s⟫_ℂ = ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε)) ∧
      (∀ k ∈ Kset ε, ∀ x y : S, (y : H) = σ k x → T y = σ k (T x)) ∧ T ≠ 0 := by
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  obtain ⟨v, hvS, hv0, -⟩ := hK.2.2.2.1
  have humat : Continuous (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1.continuous
  have hcont : ∀ s : H, Continuous (fun g : UJ ε => σ (umat g) s) := fun s =>
    (hσ.2.2 s).comp_continuous humat (fun g => g.2)
  have hre : Continuous (fun g : UJ ε => (⟪v, σ (umat g) v⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner (hcont v))
  have hone : 0 < (⟪v, σ (umat (1 : UJ ε)) v⟫_ℂ).re := by
    have : σ (umat (1 : UJ ε)) = 1 := hσ.1.1
    rw [this]
    exact re_inner_self_pos (𝕜 := ℂ).2 hv0
  obtain ⟨a, ha, ha0, ha1, hac, haU, haK⟩ := exists_conjInvariant_bump n ε
    {g | 0 < (⟪v, σ (umat g) v⟫_ℂ).re} ((isOpen_lt continuous_const hre).mem_nhds hone)
  have hacont : Continuous (fun g : UJ ε => a (umat g)) := ha.continuous.comp humat
  have hacC : Continuous (fun g : UJ ε => (a (umat g) : ℂ)) := Complex.continuous_ofReal.comp hacont
  have hsuppC : HasCompactSupport (fun g : UJ ε => (a (umat g) : ℂ)) :=
    hac.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hint : ∀ s : H, Integrable (fun g : UJ ε => (a (umat g) : ℂ) • σ (umat g) s) (muG ε) :=
    fun s => (hacC.smul (hcont s)).integrable_of_hasCompactSupport hsuppC.smul_right
  let T : S →ₗ[ℂ] H :=
    { toFun := fun s => ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)
      map_add' := by
        intro s t
        rw [← integral_add (hint s) (hint t)]
        simp only [Submodule.coe_add, map_add (f := _), smul_add]
      map_smul' := by
        intro c s
        rw [RingHom.id_apply, ← integral_smul]
        simp only [Submodule.coe_smul, map_smul, smul_comm c] }
  have hT : ∀ (s : S) (u : H), ⟪u, T s⟫_ℂ =
      ∫ g : UJ ε, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro s u
    show ⟪u, ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)⟫_ℂ = _
    rw [← integral_inner (hint s)]
    simp only [inner_smul_right]
  refine ⟨fun y => (a y : ℂ), T, ?_, hsuppC, hT, ?_, ?_⟩
  · intro g₀ _
    refine ⟨Set.univ, fun y => (a y : ℂ), isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    exact (Complex.ofRealCLM.contDiff.comp ha).contDiffOn
  · intro k hk s s' hs'
    have hu : k ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact (maximal_compact_facts n ε).1 k hk
    obtain ⟨κ, rfl⟩ := hu
    show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s' ∂(muG ε) =
      σ (umat κ) (∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint s), hs']
    have e1 : ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) (σ (umat κ) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_right_eq_self
        (fun g : UJ ε => (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (g * κ)) = _ := hσ.1.2 (umat g) g.2 (umat κ) κ.2
      rw [this, mul_inv_cancel_right]
      rfl
    have e2 : ∫ g : UJ ε, σ (umat κ) ((a (umat g) : ℂ) • σ (umat g) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_left_eq_self
        (fun g : UJ ε => (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (κ * g)) = _ := hσ.1.2 (umat κ) κ.2 (umat g) g.2
      rw [this, inv_mul_cancel_left, map_smul]
      rfl
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext g
    have hk' : umat κ⁻¹ ∈ Kset ε := (KG ε).inv_mem (x := κ) hk
    have : a (umat (κ⁻¹ * g)) = a (umat (g * κ⁻¹)) := haK _ hk' (umat g)
    rw [this]
  · intro h0
    have h1 := hT ⟨v, hvS⟩ v
    rw [h0, LinearMap.zero_apply, inner_zero_right] at h1
    have hi : Integrable (fun g : UJ ε => (a (umat g) : ℂ) * ⟪v, σ (umat g) v⟫_ℂ) (muG ε) :=
      (hacC.mul (continuous_const.inner (hcont v))).integrable_of_hasCompactSupport hsuppC.mul_right
    have h2 := congrArg Complex.re h1
    have h3 := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    rw [← h3] at h2
    have h4 : 0 < ∫ g : UJ ε, a (umat g) * (⟪v, σ (umat g) v⟫_ℂ).re ∂(muG ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        (hacont.mul hre) hac.mul_right ?_ (mul_ne_zero ha1 hone.ne')
      intro g
      by_cases h : a (umat g) = 0
      · simp [h]
      · exact mul_nonneg (ha0 _) (le_of_lt (haU g h))
    rw [← h2] at h4
    simp at h4

theorem exists_isDer_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ μ S → ∃ (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (S' : Submodule ℂ H), IsDer ε σ V E ∧ IsKTypeOf ε σ μ S' ∧ S' ≤ V := by
  intro n ε μ H _ _ _ σ S hσ hK
  let G : Set H := {v | ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), SmoothOnG ε α ∧
    HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
    ∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ}
  have hder : ∀ v ∈ Submodule.span ℂ G, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X →
      ∃ v' ∈ Submodule.span ℂ G,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
    intro v hv X hX
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      obtain ⟨β, v', k1, k2, k3, k4⟩ :=
        (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).2 X hX
      exact ⟨v', Submodule.subset_span ⟨β, s, k1, k2, k3⟩, k4⟩
    | zero => exact ⟨0, zero_mem _, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', hda⟩ := ha
      obtain ⟨b', hb', hdb⟩ := hb
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      simp only [map_add (f := _)]
      exact hda.add hdb
    | smul c a _ ha =>
      obtain ⟨a', ha', hda⟩ := ha
      refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
      simp only [map_smul]
      exact hda.const_smul c
  have hzero := GlobalTheory.DerEx.smoothOnG_zero ε
  have hsm : ∀ v ∈ Submodule.span ℂ G, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ) := by
    intro v hv y
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      exact (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).1 y
    | zero => simpa using hzero
    | add a b _ _ ha hb => simpa [inner_add_right] using GlobalTheory.DerEx.smoothOnG_comb 1 ha hb
    | smul c a _ ha => simpa [inner_smul_right] using GlobalTheory.DerEx.smoothOnG_comb c ha hzero
  obtain ⟨E, hE⟩ := GlobalTheory.DerOf.exists_isDer n ε H σ (Submodule.span ℂ G) hσ hder hsm
  obtain ⟨α, T, h1, h2, h3, h4, h5⟩ := exists_garding_kMap n ε μ H σ S hσ hK
  haveI := hK.1
  refine ⟨_, E, _, hE, GlobalTheory.Dec.FormF.rangeType n ε μ H σ S H σ (LinearMap.toContinuousLinearMap T) hK h4
    (fun h => h5 (LinearMap.ext fun x => DFunLike.congr_fun h x)), ?_⟩
  rintro _ ⟨s, rfl⟩
  exact Submodule.subset_span ⟨α, s, h1, h2, fun y => (h3 s y).symm⟩

end GlobalTheory.SmoothKType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps

section

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.MultGap

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem proj_comm (hU : IsURepOn (Kset ε) σ) {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : IsKStableOn ε σ W) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : H) :
    W.starProjection (σ k x) = σ k (W.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW k hk _ (W.starProjection_apply_mem x))
    fun w hw => ?_
  rw [← map_sub, FormF.inner_rep_K hU hk]
  exact W.starProjection_inner_eq_zero x _ (hW _ (Kset_star ε hk) w hw)

theorem orth_of_ne (hU : IsURepOn (Kset ε) σ) {Λ μ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) (hT : IsKTypeOf ε σ μ T) (hne : μ ≠ Λ) :
    ∀ x ∈ S, ∀ y ∈ T, ⟪x, y⟫_ℂ = 0 := by
  haveI := hT.1
  let Q : S →L[ℂ] H := T.starProjection.comp S.subtypeL
  by_cases hQ : Q = 0
  · intro x hx y hy
    have h1 : T.starProjection x = 0 := congrArg (fun A : S →L[ℂ] H => A ⟨x, hx⟩) hQ
    have h2 := T.starProjection_inner_eq_zero x y hy
    rwa [h1, sub_zero] at h2
  exfalso
  have hR := FormF.rangeType n ε Λ H σ S H σ Q hS (fun k hk x y hxy => by
    change T.starProjection (y : H) = σ k (T.starProjection (x : H))
    rw [hxy, proj_comm hU hT.2.1 hk]) hQ
  have hle : LinearMap.range (Q : S →ₗ[ℂ] H) ≤ T := by
    rintro _ ⟨x, rfl⟩
    exact T.starProjection_apply_mem _
  obtain ⟨v, hv, hv0, hvw⟩ := hR.2.2.2.1
  rcases hT.2.2.1 _ hle hR.2.1 with h | h
  · rw [h] at hv
    exact hv0 hv
  · obtain ⟨w, hw, hw0, hww⟩ := hT.2.2.2.1
    refine hne (GlobalTheory.LowHW.cdom_antisymm (ε := ε) (hR.2.2.2.2 μ w (h ▸ hw) hw0 hww)
      (hT.2.2.2.2 Λ v (hle hv) hv0 hvw))

theorem exists_orth (hU : IsURepOn (Kset ε) σ) {Λ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) (hT : IsKTypeOf ε σ Λ T) (hne : S ≠ T) :
    ∃ R : Submodule ℂ H, IsKTypeOf ε σ Λ R ∧ ∀ x ∈ R, ∀ y ∈ T, ⟪x, y⟫_ℂ = 0 := by
  haveI := hT.1
  let Q : S →L[ℂ] H := S.subtypeL - T.starProjection.comp S.subtypeL
  have hQa : ∀ x : S, Q x = (x : H) - T.starProjection (x : H) := fun x => rfl
  have hQ : Q ≠ 0 := by
    intro hQ
    have hle : S ≤ T := by
      intro x hx
      have h1 := hQa ⟨x, hx⟩
      rw [hQ] at h1
      have h2 : x = T.starProjection x := sub_eq_zero.1 h1.symm
      rw [h2]
      exact T.starProjection_apply_mem _
    rcases hT.2.2.1 _ hle hS.2.1 with h | h
    · obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
      rw [h] at hv
      exact hv0 hv
    · exact hne h
  refine ⟨_, FormF.rangeType n ε Λ H σ S H σ Q hS (fun k hk x y hxy => by
    rw [hQa, hQa, hxy, proj_comm hU hT.2.1 hk, map_sub]) hQ, ?_⟩
  rintro _ ⟨x, rfl⟩ y hy
  exact T.starProjection_inner_eq_zero x y hy

theorem exists_gap {lam : Fin n → ℝ} (hl : StrictAnti lam)
    (h : ∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) :
    ∃ g : ℝ, (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) ∧ 2 * (n : ℝ) < g := by
  have key : ∀ᶠ g in nhdsWithin (2 * (n : ℝ)) (Set.Ioi (2 * (n : ℝ))),
      ∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b := by
    simp only [Filter.eventually_all]
    intro a b hab he
    have h1 := h a b he
    rw [abs_of_pos (sub_pos.2 (hl hab))] at h1
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds ((eventually_lt_nhds h1).mono fun g hg => hg.le)
  exact (key.and self_mem_nhdsWithin).exists

theorem kSpan_smul_le {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (c : ℂ)
    (u : V) : kSpan ε E (c • u) ≤ kSpan ε E u :=
  sInf_le_sInf fun S hS => ⟨S.smul_mem c hS.1, hS.2⟩

theorem cas_mem_cyc {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (u : V) : Cas E u ∈ cyc E u := by
  rw [cyc, Submodule.mem_sInf]
  intro W hW
  simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply]
  exact W.sum_mem fun a _ => W.sum_mem fun b _ => hW.2 _ _ _ (hW.2 _ _ _ hW.1)

theorem cas_kHighest {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u) : KHighest ε E μ (Cas E u) := by
  have hc : ∀ a b, E a b (Cas E u) = Cas E (E a b u) := fun a b =>
    (congrArg (fun A : Module.End ℂ V => A u) ((casCentral _ n ε E hE).1 a b)).symm
  exact ⟨fun a => by rw [hc, hu.1 a, map_smul], fun a b h1 h2 => by rw [hc, hu.2 a b h1 h2, map_zero]⟩

theorem cas_real {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) (hU : IsUnitary ε E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u) (hu0 : u ≠ 0) {c : ℂ}
    (hc : Cas E u = c • u) : ∃ r : ℝ, Cas E u = (r : ℂ) • u := by
  have h := wdCas V n ε E μ u hE hU hu
  rw [hc, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  generalize ((nsq (μ + rhoC ε) - nsq (rhoC ε)) * ‖u‖ ^ 2 -
      ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) : ℝ) = t at h
  refine ⟨t / ‖u‖ ^ 2, ?_⟩
  have hn : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by simpa using hu0
  rw [hc]
  congr 1
  push_cast
  rw [← h, eq_div_iff (pow_ne_zero 2 hn)]
  rfl

theorem isKTypeOf_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → (∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) := by
  intro n ε lam H _ _ σ hl hDS hgap
  obtain ⟨hc, -, hU, hirr, -, ⟨S0, hS0⟩, -⟩ := id hDS
  have hK := FormF.URep_K hU
  obtain ⟨V, E, S, hD, hS, hSV⟩ := GlobalTheory.SmoothKType.exists_isDer_kType n ε _ H σ S0 hU hS0
  obtain ⟨hk1, hk2⟩ := GlobalTheory.Jet.KType.kType_iff n ε H σ V E hU hD
  obtain ⟨v, hv, hv0, hvw⟩ := hS.2.2.2.1
  obtain ⟨u, rfl⟩ : ∃ u : V, (u : H) = v := ⟨⟨v, hSV hv⟩, rfl⟩
  have hu0 : u ≠ 0 := fun h => hv0 (by rw [h]; rfl)
  obtain ⟨huH, huS, hufd⟩ := hk2 _ S u hS hSV hv hu0 hvw
  obtain ⟨g, hg1, hg2⟩ := exists_gap hl.1 hgap
  have hm : ∀ x ∈ cyc E u, KHighest ε E (lowK ε lam) x → ∃ c : ℂ, x = c • u :=
    GlobalTheory.Jet.kHighest_eq_smul_of_minus_killed V n ε E lam g u hD.1 hD.2.1 huH hufd hg1 hg2
      (GlobalTheory.Jet.Schmid.mul_vminus_eq_zero n ε H σ V E lam u hl hDS hD huH hufd)
  obtain ⟨c, hcu⟩ := hm _ (cas_mem_cyc E u) (cas_kHighest hD.1 huH)
  obtain ⟨r, hr⟩ := cas_real hD.1 hD.2.1 huH hu0 hcu
  have hdense := GlobalTheory.CycDense.cyc_dense n ε H σ V E _ r u hU hD hirr hu0 huH hufd hr
  obtain ⟨-, -, hst, -, hpc, hcp, hfd⟩ := pfilFacts V n ε E u hD.1
  have huniq : ∀ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T → T = S := by
    intro T hT
    by_contra hne
    obtain ⟨R, hR, hRS⟩ := exists_orth hK hT hS hne
    obtain ⟨w, hw, hw0, -⟩ := hR.2.2.2.1
    refine hw0 (hdense.eq_zero_of_inner_left ℂ fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨j, hj⟩ := hcp z hz
    haveI := hfd hufd j
    obtain ⟨m, x, μ, hx, -, hsup⟩ := kDecomp V n ε E _ (hfd hufd j) (glRel_kRel ε E hD.1)
      (isUnitary_kUnit ε E hD.2.1) (hst j)
    have hle : pfil ε E u j ≤ LinearMap.ker ((innerSL ℂ w : H →L[ℂ] ℂ).toLinearMap ∘ₗ V.subtype) := by
      rw [← hsup]
      refine iSup_le fun i y hy => ?_
      change ⟪w, (y : H)⟫_ℂ = 0
      by_cases hμ : μ i = lowK ε lam
      · obtain ⟨d, hd⟩ := hm (x i) (hpc j (hx i).1) (hμ ▸ (hx i).2.2)
        rw [hd] at hy
        exact hRS w hw _ (huS ▸ ⟨y, kSpan_smul_le E d u hy, rfl⟩)
      · have hfi : FiniteDimensional ℂ (kSpan ε E (x i)) :=
          Submodule.finiteDimensional_of_le (S₂ := pfil ε E u j) (sInf_le ⟨(hx i).1, hst j⟩)
        exact orth_of_ne hK hR (hk1 _ _ (hx i).2.1 (hx i).2.2 hfi) hμ w hw _ ⟨y, hy, rfl⟩
    exact hle hj
  have : lowKSub ε lam σ = S := le_antisymm (sSup_le fun T hT => (huniq T hT).le) (le_sSup hS)
  rw [this]
  exact hS

end GlobalTheory.Jet.MultGap
end
end
end

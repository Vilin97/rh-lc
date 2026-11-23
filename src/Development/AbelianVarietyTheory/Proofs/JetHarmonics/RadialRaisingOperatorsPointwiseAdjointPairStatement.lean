module

public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Formalism.HermitianCurvature.ActualZetaSmooth
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypothesesStatement
public import Formalism.HermitianCurvature.StatementNF
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBounded
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.VanishAbstract
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CsliceContinuous
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFderivChiBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HsInnerAddSmulRight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactZetaLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableOfContinuousOnZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairAtTAdjCpt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DoubleCosetOfZetaEq

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem doubleCoset_of_zeta_eq :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g g' : Q.Mx P.k P.r), (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' → (c, g') ∈ Q.DomR P.k P.r Bs.z Bs.z' → P5.zeta P.k P.r Bs.z Bs.z' g = P5.zeta P.k P.r Bs.z Bs.z' g' → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z', g' = h * g * h' := by
  intro Wp Wq _ _ _ _ _ _ P Bs c g g' hg hg' hζ
  obtain ⟨a, ha, b, hb, e⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec
    hg.2.1 hg.2.2
  obtain ⟨a', ha', b', hb', e'⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec
    hg'.2.1 hg'.2.2
  unfold P5.zeta at hζ
  dsimp only at e e'
  rw [← hζ] at e'
  generalize NF.muZ P.k P.r Bs.μsec (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g) = m at e e'
  refine ⟨a' * a⁻¹, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul ha' (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv ha), b⁻¹ * b',
    Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hb) hb', ?_⟩
  have h1 := Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul ha
  have h2 := Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hb
  rw [e', e]
  calc a' * m * b' = a' * (a⁻¹ * a) * m * (b * b⁻¹) * b' := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
    _ = a' * a⁻¹ * (a * m * b) * (b⁻¹ * b') := by simp only [Matrix.mul_assoc]

end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjRaisingProjEqSmul

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.RaiseFormula

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem up_unique {j : ℕ} {a b c : M.Ty P} (h : M.Up P j a b) (h' : M.Up P j a c) : b = c := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

theorem up_index {l j : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b)
    (h' : M.Up P j a b) : j = l := by
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h2 := h' ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1 h2
  by_contra hne
  rw [if_neg (fun x => hne x.symm)] at h2
  omega

theorem up_ne {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b) : b ≠ a := by
  rw [Finset.mem_Icc] at hl
  rintro rfl
  have h1 := h ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1
  omega

omit [StarRing A] in
theorem sum_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) : ∑ ρ, NF.proj κ ρ = 1 := by
  unfold NF.proj

  rw [← map_sum, ← map_one κ]
  congr 1
  funext x
  simp [Finset.sum_apply]

omit [StarRing A] in
theorem kap_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (f : M.Ty P → ℂ) (ρ : M.Ty P) :
    κ f * NF.proj κ ρ = f ρ • NF.proj κ ρ := by
  unfold NF.proj
  rw [← map_mul, ← map_smul]
  congr 1
  funext x
  by_cases h : x = ρ <;> simp [h]

omit [StarRing A] in
theorem proj_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) {ρ ρ' : M.Ty P} (h : ρ' ≠ ρ) :
    NF.proj κ ρ' * NF.proj κ ρ = 0 := by
  have := kap_mul_proj κ (fun x => if x = ρ' then 1 else 0) ρ
  rw [if_neg (Ne.symm h), zero_smul] at this
  exact this

theorem proj_SS_proj (d : Q.NFData P A) (hd : d.Rel) {j : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P j ρ ρ') :
    NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ = 0 := by
  have h1 := hd.2.2.2.1 j (fun a => if M.Up P j a ρ' then 1 else 0) (fun x => if x = ρ' then 1 else 0) (by
    intro a b hab
    by_cases hb : b = ρ'
    · subst hb; simp [hab]
    · have : ¬ M.Up P j a ρ' := fun h' => hb (up_unique hab h')
      simp [hb, this])
  have h2 : NF.proj d.κ ρ' * d.SS j = _ := h1
  rw [h2, mul_assoc, kap_mul_proj, if_neg h, zero_smul, mul_zero]

theorem proj_raising_proj_eq_smul (d : Q.NFData P A) (hd : d.Rel) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ)
    {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ =
      M.xEx P {l} ρ Y • (NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ) := by
  have hq : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have hc : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (NF.proj d.κ ρ') g := fun g hg => hd.2.1 _ g hg
  have c1 : Commute (NF.proj d.κ ρ') d.L.GG := hc _ (by simp [LevelData.fns])
  have c2 : Commute (NF.proj d.κ ρ') d.L.GGi := hc _ (by simp [LevelData.fns])
  have c3 : Commute (NF.proj d.κ ρ') d.L.ζb := hc _ (by simp [LevelData.fns])
  have c4 : Commute (NF.proj d.κ ρ') d.L.nab := hc _ (by simp)
  have c5 : Commute (NF.proj d.κ ρ') (d.x Y) := by
    unfold NF.proj Q.NFData.x
    exact (Commute.all _ _).map d.κ
  have c6 : Commute (NF.proj d.κ ρ') (d.L.l0 Y) := by
    unfold LevelData.l0
    exact c4.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right (c3.mul_right c2))
  have c7 := (c1.mul_right c5).mul_right c6
  rw [hq, mul_add, add_mul, c7.eq, mul_assoc _ (NF.proj d.κ ρ'), proj_mul_proj _ (up_ne hl h), mul_zero, zero_add]
  unfold Q.NFData.weightedSumBis
  have key : ∀ j, NF.proj d.κ ρ' * (d.SS j * d.κ fun ρ => M.xEx P {j} ρ Y) * NF.proj d.κ ρ =
      M.xEx P {j} ρ Y • (NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ) := by
    intro j
    rw [← mul_assoc, mul_assoc _ (d.κ _), kap_mul_proj, mul_smul_comm]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l]
  · exact key l
  · intro j _ hj
    rw [key, proj_SS_proj d hd (fun h' => hj (up_index hl h h')), smul_zero]
  · intro h'; exact absurd hl h'

theorem xEx_ne_zero (ex : Finset ℕ) (ρ : M.Ty P) (Y : ℂ) (h : M.xC P ρ Y ≠ 0) : M.xEx P ex ρ Y ≠ 0 := by
  unfold M.xC at h
  unfold M.xEx
  rw [Finset.prod_ne_zero_iff] at h ⊢
  exact fun i hi => h i (Finset.mem_sdiff.1 hi).1

theorem ss_formula : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Y : ℂ, (∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0) → ∃ co : M.Ty P → M.Ty P → ℂ, d.SS l = ∑ ρ, ∑ ρ', co ρ ρ' • (NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ) := by
  intro P A _ _ _ _ d hd l hl Y hY
  have hr : d.Rel := hd.2.2.1
  refine ⟨fun ρ ρ' => if M.Up P l ρ ρ' then (M.xEx P {l} ρ Y)⁻¹ else 0, ?_⟩
  have h0 : d.SS l = ∑ ρ, ∑ ρ', NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_proj, one_mul, mul_one]
  refine h0.trans (Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_)
  by_cases h : M.Up P l ρ ρ'
  · simp only [if_pos h]
    rw [proj_raising_proj_eq_smul d hr hl Y h, smul_smul, inv_mul_cancel₀ (xEx_ne_zero _ _ _ (hY ρ)), one_smul]
  · simp only [if_neg h]
    rw [zero_smul, proj_SS_proj d hr h]

end GlobalTheory.HatNF.RaiseFormula
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialRaisingOperatorsPointwiseAdjointPair

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.HatNF.RaiseAdj

open Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section gen

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

def Van (c : Fin r → ℂ) (K : Set (Q.Mx k r)) (Φ : Q.RadSp k r z z' π π') : Prop :=
  ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K → (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = 0

theorem int_left {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hKc : IsCompact K) (hKG : K ⊆ {g | 0 < Q.GGl k r z z' g})
    (Φ Ψ : Q.RadSp k r z z' π π') (hΦ : Van c K Φ) :
    Integrable (fun x : Mt k r => B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ := by
  simp only [hsInner_eq_sum]
  exact integrable_finsetSum _ fun m _ => int_cpt_gen μ hμ Φ Ψ c _ K hKc hKG hc _ (Or.inr rfl) hΦ

theorem int_right {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hKc : IsCompact K) (hKG : K ⊆ {g | 0 < Q.GGl k r z z' g})
    (Φ Ψ : Q.RadSp k r z z' π π') (hΨ : Van c K Ψ) :
    Integrable (fun x : Mt k r => B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ := by
  simp only [hsInner_eq_sum]
  exact integrable_finsetSum _ fun m _ => int_cpt_gen μ hμ Ψ Φ c _ K hKc hKG hc _ (Or.inl rfl) hΨ

def adjSub {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hKc : IsCompact K) (hKG : K ⊆ {g | 0 < Q.GGl k r z z' g})
    (Φ Ψ : Q.RadSp k r z z' π π') (hΦ : Van c K Φ) (hΨ : Van c K Ψ) :
    Submodule ℂ (Q.Pr (Q.RadSp k r z z' π π')) where
  carrier := {b | pairAt μ (b.1 Φ) Ψ c = pairAt μ Φ ((star b).1 Ψ) c}
  zero_mem' := by
    show pairAt μ 0 Ψ c = pairAt μ Φ 0 c
    have h1 := pairAt_smul_left μ (0 : Q.RadSp k r z z' π π') Ψ c 0
    have h2 := pairAt_smul_right μ Φ (0 : Q.RadSp k r z z' π π') c 0
    simp only [zero_smul, zero_mul, map_zero] at h1 h2
    rw [h1, h2]
  add_mem' := by
    intro a b ha hb
    show pairAt μ (a.1 Φ + b.1 Φ) Ψ c = pairAt μ Φ ((star a).1 Ψ + (star b).1 Ψ) c
    have h1 := pairAt_add_smul_left μ (a.1 Φ) (b.1 Φ) Ψ c 1 (int_right hμ hc hKc hKG _ _ hΨ)
      (int_right hμ hc hKc hKG _ _ hΨ)
    have h2 := pairAt_add_smul_left μ ((star a).1 Ψ) ((star b).1 Ψ) Φ c 1 (int_right hμ hc hKc hKG _ _ hΦ)
      (int_right hμ hc hKc hKG _ _ hΦ)
    simp only [one_smul, one_mul] at h1 h2
    rw [h1, pairAt_swap μ _ Φ, h2, map_add (f := _), ← pairAt_swap, ← pairAt_swap]
    exact congrArg₂ _ ha hb
  smul_mem' := by
    intro s b hb
    show pairAt μ ((s • b).1 Φ) Ψ c = pairAt μ Φ ((star (s • b)).1 Ψ) c
    rw [star_smul, Formalism.FourierDecayAlt.P.NFx4.NO.fst_smul, Formalism.FourierDecayAlt.P.NFx4.NO.fst_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      pairAt_smul_left, pairAt_smul_right]
    have hb' : pairAt μ (b.1 Φ) Ψ c = pairAt μ Φ ((star b).1 Ψ) c := hb
    rw [hb']
    simp

theorem exists_compact (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    {S : Set ℂ} (hS : IsCompact S) (hS' : S ⊆ {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}) :
    ∃ K : Set (Q.Mx k r), IsCompact K ∧ K ⊆ {g | 0 < Q.GGl k r z z' g} ∧
      ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K → Q.zetaL k r z z' (Fin.last r) g ∉ S := by
  obtain ⟨ε, hε, h1⟩ := hS.exists_forall_le' (f := fun ζ => Complex.normSq ζ - Tz k r z * Tz k r z') (a := 0)
    (Complex.continuous_normSq.sub continuous_const).continuousOn (fun b hb => sub_pos.2 (hS' hb))
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  exact ⟨_, isCompact_zeta_le z z' hz hz' hT hT' ε R, fun g hg => lt_of_lt_of_le hε hg.2.1,
    fun g hg hgK h => hgK ⟨hg, h1 _ h, hR _ h⟩⟩

theorem van_mulZ {W : Module.End ℂ (Q.RadSp k r z z' π π')} {φ : ℂ → ℝ} (hW : NF.IsMulZ W fun ζ => (φ ζ : ℂ))
    {S : Set ℂ} (hS : tsupport φ ⊆ S) {K : Set (Q.Mx k r)}
    (hK : ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K → Q.zetaL k r z z' (Fin.last r) g ∉ S) (c : Fin r → ℂ)
    (Φ : Q.RadSp k r z z' π π') : Van c K (W Φ) := by
  intro g hg hgK
  rw [Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hW, image_eq_zero_of_notMem_tsupport (fun h => hK g hg hgK (hS h))]
  simp

theorem contOn_hs (Φ Ψ : Q.RadSp k r z z' π π') (c : Fin r → ℂ) :
    ContinuousOn (fun g : Q.Mx k r => B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)
      ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)) {g | (c, g) ∈ Q.DomR k r z z'} := by
  have hA : ∀ (Ξ : Q.RadSp k r z z' π π') (v : Wq), ContinuousOn
      (fun g : Q.Mx k r => (Ξ : Q.Fn k r (Wq →L[ℂ] Wp)) c g v) {g | (c, g) ∈ Q.DomR k r z z'} := by
    intro Ξ v
    have h1 := (radSp_continuousOn Ξ).comp
      ((continuous_const.prodMk continuous_id : Continuous fun g : Q.Mx k r => (c, g)).continuousOn :
        ContinuousOn _ {g | (c, g) ∈ Q.DomR k r z z'}) (fun x hx => hx)
    exact h1.clm_apply continuousOn_const
  simp only [hsInner_eq_sum]
  exact continuousOn_finsetSum _ fun m _ => (hA Ψ _).inner (hA Φ _)

end gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem pairAt_of_ptAdj {b : RA P Bs} (hb : PtAdj P Bs b) (μ : Measure (Mt P.k P.r))
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) :
    pairAt μ (b.1 Φ) Ψ c = pairAt μ Φ ((star b).1 Ψ) c := by
  unfold pairAt
  congr 1
  funext x
  by_cases hx : (c, Matrix.of x) ∈ Q.DomR P.k P.r Bs.z Bs.z'
  · exact hb Φ Ψ _ hx
  · rw [radSp_zero_off (b.1 Φ) hx, radSp_zero_off Φ hx, hsInner_zero_left, hsInner_zero_left]

theorem hs_inv (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g g' : Q.Mx P.k P.r)
    (hg : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z') (hg' : (c, g') ∈ Q.DomR P.k P.r Bs.z Bs.z')
    (hζ : P5.zeta P.k P.r Bs.z Bs.z' g = P5.zeta P.k P.r Bs.z Bs.z' g') :
    B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) =
      B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g') ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g') := by
  obtain ⟨h, hh, h', hh', rfl⟩ := GlobalTheory.HatNF.doubleCoset_of_zeta_eq Wp Wq P Bs c g g' hg hg' hζ
  have e1 := Φ.2.2.2 (c, g) hg h hh h' hh'
  have e2 := Ψ.2.2.2 (c, g) hg h hh h' hh'
  simp only at e1 e2
  rw [e1, e2, Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (Bs.π_unitary _ hh),
    Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (Bs.π'_unitary _ hh')]

theorem triple (μ : Measure (Mt P.k P.r)) (c : Fin P.r → ℂ) (a t b : RA P Bs) (ha : PtAdj P Bs a)
    (hb : PtAdj P Bs b) (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (ht : pairAt μ (t.1 (b.1 Φ)) ((star a).1 Ψ) c = pairAt μ (b.1 Φ) ((star t).1 ((star a).1 Ψ)) c) :
    pairAt μ ((a * t * b).1 Φ) Ψ c = pairAt μ Φ ((star (a * t * b)).1 Ψ) c :=
  ((pairAt_of_ptAdj ha μ (t.1 (b.1 Φ)) Ψ c).trans ht).trans (pairAt_of_ptAdj hb μ Φ _ c)

theorem ptAdj_SS : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), PtAdj P Bs (d.SS l) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hNF l hl
  have hP := hD.1
  have hμ := hD.2.1
  have hH := (GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hNF).1
  have hκ := fun f => (GlobalTheory.HatNF.kappa_ptAdj_ptB Wp Wq P Bs X μ L st l0 d hD hNF f).1
  obtain ⟨co, hco⟩ := GlobalTheory.HatNF.RaiseFormula.ss_formula P _ d hH l hl Complex.I
    (fun ρ => Formalism.FourierDecayAlt.P.NFx4.SX.xC_ne ρ _ (by simp))

  have hmul : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → ∃ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      NF.IsMulZ W (fun ζ => (φ ζ : ℂ)) ∧ (∀ g, Commute (d.κ g).1 W) ∧ Commute (d.SS l).1 W ∧
        Commute (star (d.SS l)).1 W := by
    intro φ hφ
    have hf : ContDiff ℝ ∞ (fun ζ => (φ ζ : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    obtain ⟨W, hW⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P _ _ _ _ hP _ hf.contDiffOn
    obtain ⟨W1, hW1⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P _ _ _ _ hP _ (dZ_contDiff hf).contDiffOn
    obtain ⟨W2, hW2⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P _ _ _ _ hP _ (dZb_contDiff hf).contDiffOn
    have h := Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P _ _ _ _ hP X d hNF.1 hNF.2.1 hNF.2.2.1 hNF.2.2.2 _
      hf.contDiffOn W W1 W2 hW hW1 hW2
    exact ⟨W, hW, h.1, (h.2.1 l hl).1, (h.2.1 l hl).2⟩
  rintro Φ Ψ ⟨c, g0⟩ hx
  have hc : c ∈ OmX P.r := hx.1
  have hO : IsOpen {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  obtain ⟨ψ, hψS, hψc, hψd, -, hψ1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (x := P5.zeta P.k P.r Bs.z Bs.z' g0) (hO.mem_nhds (sub_pos.1 hx.2.2))
  obtain ⟨V, hV, hVκ, hVS, hVS'⟩ := hmul ψ hψd
  have key := GlobalTheory.HatNF.ZetaVanish.zeta_vanish Wp Wq P Bs μ c (fun g =>
    B.hsInner (((d.SS l).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((V Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) -
    B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g)
      (((star (d.SS l)).1 (V Ψ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g)) hμ
    ((contOn_hs _ _ c).sub (contOn_hs _ _ c))
    (fun g g' hg hg' hζ => by rw [hs_inv _ _ c g g' hg hg' hζ, hs_inv Φ _ c g g' hg hg' hζ]) ?_ g0 hx
  · have e : (star (d.SS l)).1 (V Ψ) = V ((star (d.SS l)).1 Ψ) := LinearMap.congr_fun hVS'.eq Ψ
    rw [e, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hV, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hV] at key
    unfold P5.zeta at hψ1
    rw [hψ1, Complex.ofReal_one, one_smul, one_smul] at key
    exact sub_eq_zero.1 key
  intro φ hφd hφc hφS
  obtain ⟨W, hW, hWκ, hWS, hWS'⟩ := hmul φ hφd
  obtain ⟨K, hKc, hKG, hK⟩ := exists_compact Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos
    (hφc.isCompact.union hψc.isCompact) (Set.union_subset hφS hψS)
  have vW := van_mulZ hW Set.subset_union_left hK c
  have vV := van_mulZ hV Set.subset_union_right hK c
  have hmem : d.SS l ∈ adjSub hμ hc hKc hKG (W Φ) (V Ψ) (vW Φ) (vV Ψ) := by
    rw [hco]
    refine Submodule.sum_mem _ fun ρ _ => Submodule.sum_mem _ fun ρ' _ => Submodule.smul_mem _ _ ?_
    rw [← hNF.2.2.2]
    refine triple μ c _ _ _ (hκ _) (hκ _) _ _ ?_
    refine pairAt_t_adj_cpt' P _ _ _ _ hP X μ hμ _ _ c hc ⟨K, hKc, hKG, fun g hg hgK => ⟨?_, ?_⟩⟩ Complex.I 1 0
    · have e := LinearMap.congr_fun (hWκ fun ρ' => if ρ' = ρ then 1 else 0).eq Φ
      simp only [Module.End.mul_apply] at e
      rw [e]
      exact vW _ g hg hgK
    · rw [hNF.2.2.1.1]
      have e := LinearMap.congr_fun (hVκ fun ρ => star (if ρ = ρ' then (1 : ℂ) else 0)).eq Ψ
      simp only [Module.End.mul_apply] at e
      rw [e]
      exact vV _ g hg hgK
  have hm : pairAt μ ((d.SS l).1 (W Φ)) (V Ψ) c = pairAt μ (W Φ) ((star (d.SS l)).1 (V Ψ)) c := hmem
  have e : (d.SS l).1 (W Φ) = W ((d.SS l).1 Φ) := LinearMap.congr_fun hWS.eq Φ
  rw [e] at hm
  have hs := integral_sub (int_left hμ hc hKc hKG (W ((d.SS l).1 Φ)) (V Ψ) (vW _))
    (int_left hμ hc hKc hKG (W Φ) ((star (d.SS l)).1 (V Ψ)) (vW _))
  unfold pairAt at hm
  rw [hm, sub_self] at hs
  rw [← hs]
  congr 1
  funext y
  rw [Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hW, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hW, hsInner_smul_left', hsInner_smul_left', mul_sub]
  rfl

end GlobalTheory.HatNF.RaiseAdj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialRaisingOperatorsPointwiseAdjointPairStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.radialRaisingOperators_pointwiseAdjointPair : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), PtAdj P Bs (d.SS l) := by
  first | exact @GlobalTheory.HatNF.RaiseAdj.ptAdj_SS | exact GlobalTheory.HatNF.RaiseAdj.ptAdj_SS | (intros; apply GlobalTheory.HatNF.RaiseAdj.ptAdj_SS <;> assumption)
end
end

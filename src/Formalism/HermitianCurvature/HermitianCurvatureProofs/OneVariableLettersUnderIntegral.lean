module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.GoodCongr

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section fam2

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem good_congr {Φ Ψ : X → V1 E} (h : Good Φ) (hΨ : ∀ v τ, τ ≠ 0 → (Ψ v : ℂ → E) τ = (Φ v : ℂ → E) τ) :
    Good Ψ := by
  refine ⟨h.1.congr fun q hq => hΨ q.1 q.2 hq.2, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  exact ⟨C, hC, fun v hv τ hτ => by rw [hΨ v τ (hK0 hτ), hz v hv τ hτ]⟩

theorem good_zero : Good (fun _ : X => (0 : V1 E)) :=
  ⟨contDiffOn_const.congr fun _ _ => rfl, fun _ _ _ => ⟨∅, isCompact_empty, fun _ _ _ _ => rfl⟩⟩

theorem good_add {Φ Ψ : X → V1 E} (h : Good Φ) (h' : Good Ψ) : Good (fun v => Φ v + Ψ v) := by
  refine ⟨(h.1.add h'.1).congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  obtain ⟨C', hC', hz'⟩ := h'.2 K hK hK0
  refine ⟨C ∪ C', hC.union hC', fun v hv τ hτ => ?_⟩
  simp only [Set.mem_union, not_or] at hv
  show (Φ v : ℂ → E) τ + (Ψ v : ℂ → E) τ = 0
  rw [hz v hv.1 τ hτ, hz' v hv.2 τ hτ, add_zero]

theorem good_smul {Φ : X → V1 E} (h : Good Φ) (c : ℂ) : Good (fun v => c • Φ v) := by
  refine ⟨(h.1.const_smul c).congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show c • (Φ v : ℂ → E) τ = 0
  rw [hz v hv τ hτ, smul_zero]

theorem good_sum {ι : Type*} (s : Finset ι) (Φ : ι → X → V1 E) (h : ∀ i ∈ s, Good (Φ i)) :
    Good (fun v => ∑ i ∈ s, Φ i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (good_zero : Good (fun _ : X => (0 : V1 E)))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem good_opM {Φ : X → V1 E} (h : Good Φ) (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) :
    Good (fun v => opM m hm (Φ v)) := by
  have hm2 : ContDiffOn ℝ ∞ (fun q : X × ℂ => m q.2) (UX X) :=
    hm.comp contDiff_snd.contDiffOn fun q hq => hq.2
  refine ⟨(hm2.smul h.1).congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show m τ • (Φ v : ℂ → E) τ = 0
  rw [hz v hv τ hτ, smul_zero]

def dzF (Φ : X → V1 E) : X → V1 E := fun v => ⟨PBP.dz (Φ v : ℂ → E), contDiffOn_wirtinger_dz (Φ v).2⟩

def dzbF (Φ : X → V1 E) : X → V1 E := fun v => ⟨PBP.dzb (Φ v : ℂ → E), contDiffOn_wirtinger_dzbar (Φ v).2⟩

theorem good_dz {Φ : X → V1 E} (h : Good Φ) : Good (dzF Φ) := by
  have hc : ContDiffOn ℝ ∞ (fun q : X × ℂ => PBP.dz (Φ q.1 : ℂ → E) q.2) (UX X) := by
    unfold PBP.dz
    exact ((cd_partial h 1).sub ((cd_partial h Complex.I).const_smul Complex.I)).const_smul _
  refine ⟨hc.congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show PBP.dz (Φ v : ℂ → E) τ = 0
  unfold PBP.dz
  rw [hz v hv τ hτ]
  simp

theorem good_dzb {Φ : X → V1 E} (h : Good Φ) : Good (dzbF Φ) := by
  have hc : ContDiffOn ℝ ∞ (fun q : X × ℂ => PBP.dzb (Φ q.1 : ℂ → E) q.2) (UX X) := by
    unfold PBP.dzb
    exact ((cd_partial h 1).add ((cd_partial h Complex.I).const_smul Complex.I)).const_smul _
  refine ⟨hc.congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show PBP.dzb (Φ v : ℂ → E) τ = 0
  unfold PBP.dzb
  rw [hz v hv τ hτ]
  simp

theorem opP_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    ((opP κ f : V1 E) : ℂ → E) τ = τ • PBP.dz (f : ℂ → E) τ + κ • (f : ℂ → E) τ := by
  show off0 (fun τ => τ • PBP.dz (f : ℂ → E) τ + κ • (f : ℂ → E) τ) τ = _
  rw [off0, if_neg hτ]

theorem opPb_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    ((opPb κ f : V1 E) : ℂ → E) τ = conj τ • PBP.dzb (f : ℂ → E) τ + κ • (f : ℂ → E) τ := by
  show off0 (fun τ => conj τ • PBP.dzb (f : ℂ → E) τ + κ • (f : ℂ → E) τ) τ = _
  rw [off0, if_neg hτ]

section ok

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

def OK (T : Module.End ℂ (V1 E)) : Prop :=
  ∀ (Φ : X → V1 E) (f : V1 E), Good Φ → IsInt μ ℓ Φ f →
    Good (fun v => T (Φ v)) ∧ IsInt μ ℓ (fun v => T (Φ v)) (T f)

variable {μ ℓ}

theorem int_add {Φ Ψ : X → V1 E} {f g : V1 E} (hℓ : Continuous ℓ) (h : Good Φ) (h' : Good Ψ)
    (hf : IsInt μ ℓ Φ f) (hg : IsInt μ ℓ Ψ g) : IsInt μ ℓ (fun v => Φ v + Ψ v) (f + g) := by
  intro τ hτ
  show (f : ℂ → E) τ + (g : ℂ → E) τ = ∫ v, ℓ v ((Φ v : ℂ → E) τ + (Ψ v : ℂ → E) τ) ∂μ
  rw [hf τ hτ, hg τ hτ, ← integral_add (good_int μ ℓ h hℓ hτ) (good_int μ ℓ h' hℓ hτ)]
  congr 1
  funext v
  rw [map_add (f := _)]

theorem int_smul {Φ : X → V1 E} {f : V1 E} (hf : IsInt μ ℓ Φ f) (c : ℂ) :
    IsInt μ ℓ (fun v => c • Φ v) (c • f) := by
  intro τ hτ
  show c • (f : ℂ → E) τ = ∫ v, ℓ v (c • (Φ v : ℂ → E) τ) ∂μ
  rw [hf τ hτ, ← integral_smul]
  congr 1
  funext v
  rw [map_smul]

theorem int_zero : IsInt μ ℓ (fun _ : X => (0 : V1 E)) 0 := by
  intro τ _
  show (0 : E) = ∫ v, ℓ v (0 : E) ∂μ
  simp

theorem int_sum {ι : Type*} (hℓ : Continuous ℓ) (s : Finset ι) (Φ : ι → X → V1 E) (f : ι → V1 E)
    (h : ∀ i ∈ s, Good (Φ i)) (hf : ∀ i ∈ s, IsInt μ ℓ (Φ i) (f i)) :
    IsInt μ ℓ (fun v => ∑ i ∈ s, Φ i v) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (int_zero : IsInt μ ℓ (fun _ : X => (0 : V1 E)) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact int_add hℓ (h a (Finset.mem_insert_self a s))
      (good_sum s Φ fun i hi => h i (Finset.mem_insert_of_mem hi)) (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem ok_zero : OK μ ℓ (0 : Module.End ℂ (V1 E)) := fun _ _ _ _ => ⟨good_zero, int_zero⟩

theorem ok_one : OK μ ℓ (1 : Module.End ℂ (V1 E)) := fun _ _ h hf => ⟨h, hf⟩

theorem ok_add (hℓ : Continuous ℓ) {T T' : Module.End ℂ (V1 E)} (h : OK μ ℓ T) (h' : OK μ ℓ T') :
    OK μ ℓ (T + T') := fun Φ f hΦ hf =>
  ⟨good_add (h Φ f hΦ hf).1 (h' Φ f hΦ hf).1, int_add hℓ (h Φ f hΦ hf).1 (h' Φ f hΦ hf).1 (h Φ f hΦ hf).2
    (h' Φ f hΦ hf).2⟩

theorem ok_mul {T T' : Module.End ℂ (V1 E)} (h : OK μ ℓ T) (h' : OK μ ℓ T') : OK μ ℓ (T * T') :=
  fun Φ f hΦ hf => h _ _ (h' Φ f hΦ hf).1 (h' Φ f hΦ hf).2

theorem ok_smul {T : Module.End ℂ (V1 E)} (h : OK μ ℓ T) (c : ℂ) : OK μ ℓ (c • T) := fun Φ f hΦ hf =>
  ⟨good_smul (h Φ f hΦ hf).1 c, int_smul (h Φ f hΦ hf).2 c⟩

theorem ok_neg {T : Module.End ℂ (V1 E)} (h : OK μ ℓ T) : OK μ ℓ (-T) := by
  rw [← neg_one_smul ℂ T]
  exact ok_smul h (-1)

theorem ok_alg (c : ℂ) : OK μ ℓ (algebraMap ℂ (Module.End ℂ (V1 E)) c) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact ok_smul ok_one c

theorem ok_opM (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) : OK μ ℓ (opM (E := E) m hm) := by
  intro Φ f hΦ hf
  refine ⟨good_opM hΦ m hm, fun τ hτ => ?_⟩
  show m τ • (f : ℂ → E) τ = ∫ v, ℓ v (m τ • (Φ v : ℂ → E) τ) ∂μ
  rw [hf τ hτ, ← integral_smul]
  congr 1
  funext v
  rw [map_smul]

theorem ok_opP (hℓ : Continuous ℓ) (κ : ℂ) : OK μ ℓ (opP (E := E) κ) := by
  intro Φ f hΦ hf
  have hg : Good (fun v => opM (fun τ => τ) cd_id (dzF Φ v) + κ • Φ v) :=
    good_add (good_opM (good_dz hΦ) _ _) (good_smul hΦ κ)
  refine ⟨good_congr hg fun v τ hτ => by rw [opP_apply κ _ hτ]; rfl, fun τ hτ => ?_⟩
  have i1 : Integrable (fun v => τ • ℓ v (PBP.dz (Φ v : ℂ → E) τ)) μ := (good_int μ ℓ (good_dz hΦ) hℓ hτ).smul τ
  have i2 : Integrable (fun v => κ • ℓ v ((Φ v : ℂ → E) τ)) μ := (good_int μ ℓ hΦ hℓ hτ).smul κ
  rw [opP_apply κ f hτ, dz_int μ ℓ hΦ hℓ hf hτ, hf τ hτ, ← integral_smul, ← integral_smul, ← integral_add i1 i2]
  congr 1
  funext v
  rw [opP_apply κ _ hτ, map_add (f := _), map_smul, map_smul]

theorem ok_opPb (hℓ : Continuous ℓ) (κ : ℂ) : OK μ ℓ (opPb (E := E) κ) := by
  intro Φ f hΦ hf
  have hg : Good (fun v => opM (fun τ => conj τ) cd_conj (dzbF Φ v) + κ • Φ v) :=
    good_add (good_opM (good_dzb hΦ) _ _) (good_smul hΦ κ)
  refine ⟨good_congr hg fun v τ hτ => by rw [opPb_apply κ _ hτ]; rfl, fun τ hτ => ?_⟩
  have i1 : Integrable (fun v => conj τ • ℓ v (PBP.dzb (Φ v : ℂ → E) τ)) μ :=
    (good_int μ ℓ (good_dzb hΦ) hℓ hτ).smul (conj τ)
  have i2 : Integrable (fun v => κ • ℓ v ((Φ v : ℂ → E) τ)) μ := (good_int μ ℓ hΦ hℓ hτ).smul κ
  rw [opPb_apply κ f hτ, dzb_int μ ℓ hΦ hℓ hf hτ, hf τ hτ, ← integral_smul, ← integral_smul, ← integral_add i1 i2]
  congr 1
  funext v
  rw [opPb_apply κ _ hτ, map_add (f := _), map_smul, map_smul]

end ok

end fam2

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.EntrywiseClassWordTransfer

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section pr

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

def PG (x : Q.Pr (V1 E)) : Prop := OK μ ℓ x.1 ∧ OK μ ℓ x.2.unop

variable {μ ℓ}

theorem pg_zero : PG μ ℓ (0 : Q.Pr (V1 E)) := ⟨ok_zero, ok_zero⟩

theorem pg_one : PG μ ℓ (1 : Q.Pr (V1 E)) := ⟨ok_one, ok_one⟩

theorem pg_add (hℓ : Continuous ℓ) {x y : Q.Pr (V1 E)} (hx : PG μ ℓ x) (hy : PG μ ℓ y) : PG μ ℓ (x + y) :=
  ⟨ok_add hℓ hx.1 hy.1, ok_add hℓ hx.2 hy.2⟩

theorem pg_mul {x y : Q.Pr (V1 E)} (hx : PG μ ℓ x) (hy : PG μ ℓ y) : PG μ ℓ (x * y) :=
  ⟨ok_mul hx.1 hy.1, ok_mul hy.2 hx.2⟩

theorem pg_neg {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : PG μ ℓ (-x) := ⟨ok_neg hx.1, ok_neg hx.2⟩

theorem pg_star {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : PG μ ℓ (star x) := ⟨hx.2, hx.1⟩

theorem pg_alg (c : ℂ) : PG μ ℓ (algebraMap ℂ (Q.Pr (V1 E)) c) := ⟨ok_alg c, ok_alg (conj c)⟩

theorem pg_sum (hℓ : Continuous ℓ) {ι : Type*} (s : Finset ι) (f : ι → Q.Pr (V1 E)) (h : ∀ i ∈ s, PG μ ℓ (f i)) :
    PG μ ℓ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (pg_zero : PG μ ℓ (0 : Q.Pr (V1 E)))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pg_add hℓ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {S : Type} [Fintype S] [DecidableEq S]


variable (μ ℓ) in
def EntrywiseClass (M : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) : Prop := ∀ a b, PG μ ℓ (M a b)

theorem entrywise_class_mul (hℓ : Continuous ℓ) {M N : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))} (hM : EntrywiseClass μ ℓ M) (hN : EntrywiseClass μ ℓ N) :
    EntrywiseClass μ ℓ (M * N) := fun a b => by
  rw [Matrix.mul_apply]
  exact pg_sum hℓ _ _ fun c _ => pg_mul (hM a c) (hN c b)

theorem entrywise_class_sum (hℓ : Continuous ℓ) {ι : Type*} (s : Finset ι) (M : ι → Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E)))
    (h : ∀ i ∈ s, EntrywiseClass μ ℓ (M i)) : EntrywiseClass μ ℓ (∑ i ∈ s, M i) := fun a b => by
  rw [Matrix.sum_apply]
  exact pg_sum hℓ _ _ fun i hi => h i hi a b

theorem entrywise_class_one : EntrywiseClass μ ℓ (1 : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun a b => by
  rw [Matrix.one_apply]
  split_ifs
  · exact pg_one
  · exact pg_zero

theorem entrywise_class_unit_matrix (a : S) (i j : Fin 2) : EntrywiseClass μ ℓ (Wd.eU a i j : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun x y => by
  unfold Wd.eU
  rw [Matrix.of_apply]
  split_ifs
  · exact pg_one
  · exact pg_zero

theorem entrywise_class_scalar {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : EntrywiseClass μ ℓ (Wd.io x : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun a b => by
  unfold Wd.io
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact pg_zero

theorem entrywise_class_insert (hℓ : Continuous ℓ) (a : S) {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E)))} (hM : ∀ i j, EntrywiseClass μ ℓ (M i j)) :
    EntrywiseClass μ ℓ (Wd.ins a M) := by
  unfold Wd.ins
  exact entrywise_class_sum hℓ _ _ fun i _ => entrywise_class_sum hℓ _ _ fun j _ => entrywise_class_mul hℓ (entrywise_class_unit_matrix a i j) (hM i j)

theorem pg_Ts (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) (Y : ℂ) : ∀ i j, PG μ ℓ (Wd.Ts σ Y i j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact pg_add hℓ (pg_alg Y) hp
  · exact pg_neg hc
  · exact hci
  · exact pg_zero

theorem entrywise_class_letter (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) (l : Wd.Letter ℂ S) : EntrywiseClass μ ℓ (Wd.vlet σ l) := by
  unfold Wd.vlet
  refine entrywise_class_insert hℓ _ fun i j => ?_
  unfold Wd.lift0
  rw [Matrix.map_apply]
  refine entrywise_class_scalar ?_
  split_ifs
  · exact pg_Ts hℓ σ hp hc hci _ i j
  · rw [Matrix.map_apply]
    exact pg_star (pg_Ts hℓ σ hp hc hci _ i j)

theorem entrywise_class_word_transfer (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) : ∀ w : List (Wd.Letter ℂ S), EntrywiseClass μ ℓ (Wd.bT σ w)
  | [] => by rw [Wd.bT]; exact entrywise_class_one
  | l :: w => by
      rw [Wd.bT]
      exact entrywise_class_mul hℓ (entrywise_class_letter hℓ σ hp hc hci l) (entrywise_class_word_transfer hℓ σ hp hc hci w)

theorem entrywise_class_site_one (hℓ : Continuous ℓ) (κ : ℂ) (w : List (Wd.Letter ℂ S)) :
    EntrywiseClass μ ℓ (Wd.bT (site1 (E := E) κ) w) :=
  entrywise_class_word_transfer hℓ _ ⟨ok_opP hℓ κ, ok_neg (ok_opPb hℓ κ)⟩ ⟨ok_opM _ cd_id, ok_opM _ cd_conj⟩
    ⟨ok_opM _ cd_inv, ok_opM _ cd_conjinv⟩ w

theorem oneBT_int (hℓ : Continuous ℓ) (κ : ℂ) (w : List (Wd.Letter ℂ S)) (Φ : X → Wd.Ix S → V1 E)
    (x : Wd.Ix S → V1 E) (hG : ∀ b, Good (fun v => Φ v b)) (hI : ∀ b, IsInt μ ℓ (fun v => Φ v b) (x b))
    (a : Wd.Ix S) :
    Good (fun v => oneBT κ w (Φ v) a) ∧ IsInt μ ℓ (fun v => oneBT κ w (Φ v) a) (oneBT κ w x a) := by
  have hB := entrywise_class_site_one (μ := μ) (ℓ := ℓ) hℓ κ w
  unfold oneBT act1
  exact ⟨good_sum _ _ fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).1,
    int_sum hℓ _ _ _ (fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).1) fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).2⟩

end pr

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.OneVariableLettersUnderIntegral

section

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem good_of_goodFam {E X S : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Φ : X → S → V1 E} (h : CutHB.GoodFam Φ) (e : S) : Good (fun v => Φ v e) := by
  refine ⟨h.1 e, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  exact ⟨C, hC, fun v hv τ hτ => hz v hv τ hτ e⟩

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.SliceIntegralLemmas

theorem one_variable_letters_under_integral : CutHB.OneBTInt := by
  intro E _ _ _ X _ _ _ _ _ μ _ ℓ hℓ S _ _ κ w Φ hΦ f hf t ht e
  exact (oneBT_int (μ := μ) hℓ κ w Φ f (good_of_goodFam hΦ) (fun b τ hτ => hf b τ hτ) e).2 t ht

end Formalism.FourierDecayAlt.P
end
end
end

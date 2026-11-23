module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraExtra

section

@[expose] public section

namespace GlobalTheory.ClosingLemmaThird

theorem main : (let d1 : {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → {κ : Type} → [Fintype κ] → ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) → (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → Prop := @(fun {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) (Φ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) ↦ ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), Φ = ∑ k : Fin m, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ (k : Fin m) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), φ k v ∈ GlobalTheory.WeilM.SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (∀ (k : Fin m), ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) in Filter.cofinite, φ k v = vac v) ∧ ∀ (k : Fin m), φ k v₁ = φ₀); ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {κ : Type} [inst_2 : Fintype κ] {vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ} {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ} {Φ Ψ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ}, d1 vac v₁ φ₀ Φ → d1 vac v₁ φ₀ Ψ → d1 vac v₁ φ₀ (Φ + Ψ)) := by
  intro d1 F _ _ κ _ vac v₁ φ₀ Φ Ψ hΦ hΨ
  obtain ⟨m, f, φ, hΦe, h1, h2, h3⟩ := hΦ
  obtain ⟨m', g, ψ, hΨe, g1, g2, g3⟩ := hΨ
  refine ⟨m + m', Fin.append f g, Fin.append φ ψ, ?_, ?_, ?_, ?_⟩
  · rw [hΦe, hΨe, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · intro k v
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h1 i v
    · simpa only [Fin.append_right] using g1 i v
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h2 i
    · simpa only [Fin.append_right] using g2 i
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h3 i
    · simpa only [Fin.append_right] using g3 i

end GlobalTheory.ClosingLemmaThird
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureSumZero

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrodTheta

variable {F : Type} [Field F] [NumberField F]

def HasTheta {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) (f : W → ℂ) : Prop :=
  ∀ x, HasSum (fun ξ : κ → F => co.rho ψ x Φ fun i => algebraMap F (AF F) (ξ i)) (f x)

def IsPureSum {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (φ₀ : (κ → Fv F v₁) → ℂ) (Φ : (κ → AF F) → ℂ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
    Φ = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in cofinite, φ k v = vac v) ∧
      ∀ k, φ k v₁ = φ₀

theorem isPureSum_zero {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ)
    (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (φ₀ : (κ → Fv F v₁) → ℂ) : IsPureSum vac v₁ φ₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0⟩

theorem IsPureSum.smul {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ) (c : ℂ) :
    IsPureSum vac v₁ φ₀ (c • Φ) := by
  obtain ⟨m, f, φ, rfl, h1, h2, h3⟩ := h
  refine ⟨m, fun k => c • f k, φ, ?_, h1, h2, h3⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  ring

theorem IsPureSum.add {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ Ψ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ)
    (h' : IsPureSum vac v₁ φ₀ Ψ) : IsPureSum vac v₁ φ₀ (Φ + Ψ) := by
  first
  | exact @_root_.GlobalTheory.ClosingLemmaThird.main
  | exact _root_.GlobalTheory.ClosingLemmaThird.main
  | (apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosingLemmaThird.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosingLemmaThird.main ..)

theorem IsPureSum.sum {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {ι : Type} (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ k ∈ s, IsPureSum vac v₁ φ₀ (Φ k)) : IsPureSum vac v₁ φ₀ (∑ k ∈ s, Φ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPureSum_zero vac v₁ φ₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

section Theta

variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
  (co : Darboux B κ) (ψ : AddChar (AF F) ℂ)

theorem rho_smul (x : W) (c : ℂ) (Φ : (κ → AF F) → ℂ) : co.rho ψ x (c • Φ) = c • co.rho ψ x Φ := by
  funext y
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem hasTheta_zero : HasTheta co ψ 0 0 := fun x => by
  have : co.rho ψ x 0 = 0 := by simpa using rho_smul co ψ x 0 0
  simpa [this] using (hasSum_zero : HasSum (fun _ : κ → F => (0 : ℂ)) 0)

variable {co ψ}

theorem HasTheta.smul {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (c : ℂ) :
    HasTheta co ψ (c • Φ) (c • f) := fun x => by
  rw [rho_smul]
  exact (h x).mul_left c

theorem HasTheta.add {Φ Ψ : (κ → AF F) → ℂ} {f g : W → ℂ} (h : HasTheta co ψ Φ f) (h' : HasTheta co ψ Ψ g) :
    HasTheta co ψ (Φ + Ψ) (f + g) := by
  intro x
  have h0 := (h x).add (h' x)
  simpa only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, mul_add] using h0

theorem HasTheta.sum {ι : Type} (s : Finset ι) {Φ : ι → (κ → AF F) → ℂ} {f : ι → W → ℂ}
    (h : ∀ k ∈ s, HasTheta co ψ (Φ k) (f k)) : HasTheta co ψ (∑ k ∈ s, Φ k) (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasTheta_zero co ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem HasTheta.thetaSum_eq {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (x : W) :
    thetaSum F (co.rho ψ x Φ) = f x :=
  (h x).tsum_eq

end Theta

end GlobalTheory.SchrodTheta

end
end
end

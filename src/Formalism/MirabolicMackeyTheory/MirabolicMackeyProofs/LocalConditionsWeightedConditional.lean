module

public import Formalism.MirabolicMackeyTheory.StatementL
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
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.GlobalBoundRefinements
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.MirabolicMackeyTheory.StatementLoc

section

@[expose] public section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

def LocalIndexLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    (∀ (Z : Type) [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
      (w : HeightOneSpectrum (𝓞 K)) (A B A' B' : Submodule (𝓞 K) Z),
      lix w A B = lix w (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) ∧
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A' →
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B' → lix w A B = lix w A' B')) ∧
    (∀ (d : ℕ) (w : HeightOneSpectrum (𝓞 K)) (A B A' B' : Submodule (𝓞 K) (Fin d → K)),
      idx w A B = idx w (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) ∧
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A' →
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B' → idx w A B = idx w A' B'))

def OnLocalAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (V₀ : Submodule K Z) (e : Z →ₗ[K] Z), e ∘ₗ e = e → LinearMap.range e = V₀ →
    ∀ (M Th ThK Th0 X₃ X₄ : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th ≤ M → Th0.FG →
    Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K) →
    (∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M) →
    (∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn (eig ρ U ψ ⊓ V₀) X₃ → IsLatIn (eig ρ U ψ ⊓ V₀) X₄ → Formalism.HermitianLatticesTheory.localization₂ w.asIdeal X₃ ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal X₄ →
    ∀ (ε : ℝ),
    (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    LinearMap.range φ = eig ρ U ψ ⊓ V₀ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M →
    Tj.map (φ.restrictScalars (𝓞 K)) = X₄ →
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε

def LocalConditionsWeightedAtPlace : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (V₀ : Submodule K Z) (e : Z →ₗ[K] Z), e ∘ₗ e = e → LinearMap.range e = V₀ →
    ∀ (M Th1 Th ThK Th0 ThJ X₃ : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th1 → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th1 ≤ Th → Th ≤ M → Th0.FG →
    Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K) →
    (∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M) →
    (∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th1) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (ThJ.map (e.restrictScalars (𝓞 K))) → Th0 ≤ ThJ →
    IsLatIn (eig ρ U ψ ⊓ V₀) X₃ →
    ∀ (X : Type) [AddCommGroup X] [Module K X] [Module (𝓞 K) X] [IsScalarTower (𝓞 K) K X]
      (θ' : X →ₗ[K] Z) (eX pr : X →ₗ[K] X) (Mt : Submodule (𝓞 K) X),
    θ' ∘ₗ eX = e ∘ₗ θ' → (∀ x ∈ LinearMap.range eX, x - pr x ∈ LinearMap.ker θ') →
    IsLatIn (eig ρ U ψ ⊓ V₀) ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) →
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal X₃ ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) →
    ∀ (ε : ℝ),
    (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    LinearMap.range φ = eig ρ U ψ ⊓ V₀ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M →
    Tj.map (φ.restrictScalars (𝓞 K)) =
      ((Mt.map (eX.restrictScalars (𝓞 K))).map (pr.restrictScalars (𝓞 K))).map (θ'.restrictScalars (𝓞 K)) →
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε

end Formalism.EigenvalueLevelCeiling
end
end
end

-- Source module: Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsWeightedConditional

section

@[expose] public section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues Formalism.HermitianLatticesTheory

section Gen

theorem locLen_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {A A' C C' : Submodule R W} (hA : localization₂ p A = localization₂ p A') (hC : localization₂ p C = localization₂ p C') :
    locLen p A C = locLen p A' C' := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [hA, hC]

private theorem mem_localization_iff_exists_smul_mem {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

private theorem locP_locP' {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p A) = Formalism.HermitianLatticesTheory.localization₂ p A := by
  ext x
  rw [mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [mem_localization_iff_exists_smul_mem] at h
    obtain ⟨t, ht, h⟩ := h
    exact ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact h⟩
  · intro hx
    exact ⟨1, p.primeCompl.one_mem, by rw [one_smul, mem_localization_iff_exists_smul_mem]; exact hx⟩

private theorem locP_inf' {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A B : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) = Formalism.HermitianLatticesTheory.localization₂ p A ⊓ Formalism.HermitianLatticesTheory.localization₂ p B := by
  ext x
  rw [Submodule.mem_inf, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [Submodule.mem_inf] at h
    exact ⟨⟨s, hs, h.1⟩, ⟨s, hs, h.2⟩⟩
  · rintro ⟨⟨s, hs, h1⟩, ⟨t, ht, h2⟩⟩
    refine ⟨t * s, p.primeCompl.mul_mem ht hs, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [mul_smul]
      exact A.smul_mem t h1
    · rw [mul_comm, mul_smul]
      exact B.smul_mem s h2

theorem lidx_locP {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (A B : Submodule R W) : lidx p A B = lidx p (localization₂ p A) (localization₂ p B) := by
  have e1 := locP_locP' p A
  have e3 := locP_locP' p B
  have e2 : Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p A ⊓ Formalism.HermitianLatticesTheory.localization₂ p B) = Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) := by
    rw [locP_inf', locP_locP', locP_locP', locP_inf']
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [locLen_congr p e1.symm e2.symm, locLen_congr p e3.symm e2.symm]

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem lix_locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] (w : HeightOneSpectrum (𝓞 K))
    (A B : Submodule (𝓞 K) Z) :
    lix w A B = lix w (localization₂ w.asIdeal A) (localization₂ w.asIdeal B) := by
  unfold lix
  exact lidx_locP _ A B

theorem locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
    (w : HeightOneSpectrum (𝓞 K)) (A X₃ X₄ : Submodule (𝓞 K) Z)
    (h : localization₂ w.asIdeal X₃ ≤ localization₂ w.asIdeal X₄) :
    lix w A (X₃ ⊓ X₄) = lix w A X₃ := by
  rw [lix_locP w A (X₃ ⊓ X₄), lix_locP w A X₃, locP_inf', inf_eq_left.mpr h]

end Gen

theorem local_conditions_weighted_at_place : LocalConditionsWeightedAtPlace := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig
    hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hpr h4 h34 ε hTW d φ hinj hrng
    Mj Tj hMj hTj
  exact local_conditions_weighted K Z w P ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ
    (X₃ ⊓ (Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K)))
    hM hTh1 hTh hThK h1le hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J
    (idxRules_inf_lat h3 h4) X θ' eX pr Mt hc hpr h4 inf_le_right ε
    (by rw [locP w _ _ _ h34]; exact hTW) d φ hinj hrng Mj Tj hMj hTj

section Instance

variable (K : Type) [Field K] [NumberField K] [StarRing K]

end Instance

end Formalism.EigenvalueLevelCeiling
end
end
end

module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SmoothVectorsTranslateUnitary

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Sm

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)}

theorem smooth_vectors_add {v1 v2 : H} (h1 : v1 ∈ smoothVecs (k := k) (r := r) σ)
    (h2 : v2 ∈ smoothVecs (k := k) (r := r) σ) : v1 + v2 ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U1, F1, o1, m1, c1, e1⟩ := h1 g₀ hg₀
  obtain ⟨U2, F2, o2, m2, c2, e2⟩ := h2 g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g + F2 g, o1.inter o2, ⟨m1, m2⟩,
    (c1.mono Set.inter_subset_left).add (c2.mono Set.inter_subset_right), fun g hg hgU => ?_⟩
  have a1 : σ g v1 = F1 g := e1 g hg.1 hgU
  have a2 : σ g v2 = F2 g := e2 g hg.2 hgU
  show σ g (v1 + v2) = F1 g + F2 g
  rw [map_add (f := _), a1, a2]

theorem smooth_vectors_smul (c : ℂ) {v : H} (h1 : v ∈ smoothVecs (k := k) (r := r) σ) :
    c • v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U1, F1, o1, m1, c1, e1⟩ := h1 g₀ hg₀
  refine ⟨U1, fun g => c • F1 g, o1, m1, c1.const_smul c, fun g hg hgU => ?_⟩
  have a1 : σ g v = F1 g := e1 g hg hgU
  show σ g (c • v) = c • F1 g
  rw [map_smul, a1]

theorem smooth_vectors_translate_unitary
    (hrep : ∀ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ (a * b) = (σ a).comp (σ b))
    {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ a v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U, F, o, m, c, e⟩ := hv (g₀ * a) (unitary_group_mul_mem hg₀ ha)
  have hR : ContDiff ℝ ∞ (fun x : Mat k r => x * a) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ a)).contDiff
  refine ⟨(fun x : Mat k r => x * a) ⁻¹' U, fun x => F (x * a), o.preimage hR.continuous, m,
    c.comp hR.contDiffOn (fun x hx => hx), fun g hg hgU => ?_⟩
  have a1 : σ (g * a) v = F (g * a) := e (g * a) hg (unitary_group_mul_mem hgU ha)
  show σ g (σ a v) = F (g * a)
  rw [← a1, hrep g hgU a ha]
  rfl

end Sm

namespace BData

variable (X : BData)

variable {X}

end BData

end Formalism.MainNotions.LeviCoordinates

end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.KfinOfMemLowKSub

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finset_sup_kstable {n : ℕ} (ε : Fin n → Bool) (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (s : Finset (Submodule ℂ H)) (hs : ∀ S ∈ s, FiniteDimensional ℂ S ∧ IsKStableOn ε τ S) :
    FiniteDimensional ℂ ↥(s.sup (id : Submodule ℂ H → Submodule ℂ H)) ∧
      IsKStableOn ε τ (s.sup (id : Submodule ℂ H → Submodule ℂ H)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · show FiniteDimensional ℂ ↥(⊥ : Submodule ℂ H)
      infer_instance
    · intro g _ v hv
      simp only [Finset.sup_empty, Submodule.mem_bot] at hv
      simp [hv]
  | insert a s ha ih =>
    have hA := hs a (Finset.mem_insert_self a s)
    have hS := ih (fun S hS' => hs S (Finset.mem_insert_of_mem hS'))
    rw [Finset.sup_insert]
    have := hA.1
    have := hS.1
    refine ⟨?_, ?_⟩
    · simp only [id]
      infer_instance
    · intro g hg v hv
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hA.2 g hg x hx) (hS.2 g hg y hy)

theorem kfin_of_mem_lowKSub {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H} (hw : w ∈ lowKSub ε lam τ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ w ∈ S ∧ IsKStableOn ε τ S := by
  obtain ⟨s, hsS, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  have h := finset_sup_kstable ε τ s (fun S hS => ⟨(hsS hS).1, (hsS hS).2.1⟩)
  refine ⟨s.sup (id : Submodule ℂ H → Submodule ℂ H), h.1, ?_, h.2⟩
  rw [Finset.sup_eq_iSup]
  exact hws

theorem kfinHpk_of_lowUnitH {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} {w : H} (hw : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨P, hP, -, hmem⟩ := hw
  obtain ⟨S, hfd, hwS, hst⟩ := kfin_of_mem_lowKSub hmem
  exact ⟨S, hfd, hwS, Formalism.MainNotions.LowestKTypeMultiplicity.kstable_Hpk hP hst⟩

theorem zero_mem_smoothVecs (σ : Mx k r → (H →L[ℂ] H)) : (0 : H) ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ _
  refine ⟨Set.univ, fun _ => (0 : H), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
  simp

def smoothSub (σ : Mx k r → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := smoothVecs (k := k) (r := r) σ
  add_mem' := fun h1 h2 => Formalism.MainNotions.LeviCoordinates.smooth_vectors_add h1 h2
  zero_mem' := zero_mem_smoothVecs σ
  smul_mem' := fun c _ h => Formalism.MainNotions.LeviCoordinates.smooth_vectors_smul c h

end Smooth

end Formalism.MainNotions.DoubleDerivativeSmoothness
end
end
end

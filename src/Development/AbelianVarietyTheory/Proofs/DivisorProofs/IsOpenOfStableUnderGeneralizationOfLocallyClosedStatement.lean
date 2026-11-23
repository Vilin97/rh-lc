module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Order.CompletePartialOrder

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfConstructible

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

def ultrafilterPrime {A : Type} [CommRing A] (U : Ultrafilter (PrimeSpectrum A)) :
    PrimeSpectrum A where
  asIdeal :=
    { carrier := {c | ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal}
      add_mem' := fun {a b} ha hb => by
        have ha' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∈ t.asIdeal := ha
        have hb' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), b ∈ t.asIdeal := hb
        exact (ha'.and hb').mono fun t ht => t.asIdeal.add_mem ht.1 ht.2
      zero_mem' := Filter.Eventually.of_forall fun t => t.asIdeal.zero_mem
      smul_mem' := fun r a ha => by
        have ha' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∈ t.asIdeal := ha
        exact ha'.mono fun t ht => t.asIdeal.mul_mem_left r ht }
  isPrime :=
    { ne_top' := fun h => by
        have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), (1 : A) ∈ t.asIdeal :=
          (Ideal.eq_top_iff_one _).1 h
        obtain ⟨t, ht⟩ := h1.exists
        exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ht)
      mem_or_mem' := fun {a b} hab => by
        have h : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a * b ∈ t.asIdeal := hab
        exact Ultrafilter.eventually_or.1 (h.mono fun t ht => t.isPrime.mem_or_mem ht) }

theorem isOpen_of_stableUnderGeneralization_of_constructible_pieces :
    ∀ (A : Type) [CommRing A] (Z : Set (PrimeSpectrum A)), StableUnderGeneralization Z → (∀ p ∈ Z, ∃ (a : A) (I : Finset A), a ∉ p.asIdeal ∧ (∀ c ∈ I, c ∈ p.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → t ∈ Z) → IsOpen Z := by
  intro A _ Z hZ hpc
  rw [isOpen_iff_mem_nhds]
  intro p hp
  by_contra hn
  have hne : (nhds p ⊓ Filter.principal Zᶜ).NeBot := by
    rw [Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot, compl_compl]
    exact hn
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (nhds p ⊓ Filter.principal Zᶜ)
  have hU1 : (U : Filter (PrimeSpectrum A)) ≤ nhds p := hU.trans inf_le_left
  have hU2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), t ∉ Z :=
    Filter.le_principal_iff.1 (hU.trans inf_le_right)
  have hle : ultrafilterPrime U ≤ p := by
    intro c hc
    by_contra hcp
    have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal := hc
    have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∉ t.asIdeal :=
      hU1 ((PrimeSpectrum.basicOpen c).isOpen.mem_nhds hcp)
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    exact ht2 ht1
  have hq : ultrafilterPrime U ∈ Z :=
    hZ ((PrimeSpectrum.le_iff_specializes _ _).1 hle |> fun h => by simpa using h) hp
  obtain ⟨a, I, ha, hI, hsub⟩ := hpc _ hq
  have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∉ t.asIdeal :=
    Ultrafilter.eventually_not.2 ha
  have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), ∀ c ∈ I, c ∈ t.asIdeal :=
    (Filter.eventually_all_finset I).2 fun c hc => hI c hc
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((h1.and h2).and hU2).exists
  exact ht3 (hsub t ht1 ht2)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyClosed

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces :
    ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by
  classical
  intro X Z hZ hpc
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have key : ∀ (p : PrimeSpectrum Γ(X, U)) (a : Γ(X, U)),
      hU.fromSpec p ∈ X.basicOpen a ↔ a ∉ p.asIdeal := by
    intro p a
    have h := hU.fromSpec_preimage_basicOpen a
    have h2 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a ↔ p ∈ PrimeSpectrum.basicOpen a := by
      rw [h]; rfl
    exact h2
  have hopen : IsOpen (X := PrimeSpectrum Γ(X, U)) (hU.fromSpec ⁻¹' Z) := by
    refine GlobalTheory.isOpen_of_stableUnderGeneralization_of_constructible_pieces Γ(X, U) _ ?_ ?_
    · intro p q hpq hp
      exact hZ (hpq.map hU.fromSpec.continuous) hp
    · intro p hp
      obtain ⟨W, W', J, hWW', hpW, hpJ, hsub⟩ := hpc _ hp
      have hpU : hU.fromSpec p ∈ U := hU.range_fromSpec.le ⟨p, rfl⟩
      obtain ⟨a, haW, hpa⟩ := hU.exists_basicOpen_le (V := W) ⟨_, hpW⟩ hpU
      have hc : ∀ c : Γ(X, W'), ∃ c' : Γ(X, U),
          X.basicOpen c' = X.basicOpen a ⊓ X.basicOpen c := by
        intro c
        obtain ⟨c', hc'⟩ := hU.basicOpen_basicOpen_is_basicOpen a
          (X.presheaf.map (homOfLE (haW.trans hWW')).op c)
        exact ⟨c', by rw [hc', Scheme.basicOpen_res]⟩
      choose g hg using hc
      refine ⟨a, J.image g, (key p a).1 hpa, ?_, ?_⟩
      · intro c' hc'
        obtain ⟨c, hcJ, rfl⟩ := Finset.mem_image.1 hc'
        by_contra hn
        have := (key p _).2 hn
        rw [hg] at this
        exact hpJ c hcJ this.2
      · intro t hta htI
        have hta' := (key t a).2 hta
        refine hsub _ (haW hta') fun c hcJ htc => ?_
        refine (key t (g c)).1 ?_ (htI _ (Finset.mem_image_of_mem g hcJ))
        rw [hg]
        exact ⟨hta', htc⟩
  refine ⟨hU.fromSpec '' (hU.fromSpec ⁻¹' Z), Set.image_preimage_subset _ _,
    hU.fromSpec.isOpenEmbedding.isOpenMap _ hopen, ?_⟩
  obtain ⟨p, rfl⟩ := hU.range_fromSpec.ge hxU
  exact ⟨p, hx, rfl⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces : ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by
  first | exact @GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces | exact GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces | (intros; apply GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces <;> assumption)
end
end

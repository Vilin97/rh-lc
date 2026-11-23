module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
public import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassGroupCoprimeRepresentative
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfIsAlgebraic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceData

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Published GlobalTheory.Mem.HD
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.HostDatumExists

theorem exists_reps (K : Type) [Field K] [NumberField K] {ι : Type} [Finite ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (c : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = c ∧
      (∀ i, IsCoprime (I : Ideal (𝓞 K)) (Ideal.span {((n i : ℕ) : 𝓞 K)})) ∧
      ∀ 𝔭 ∈ S, ¬ (I : Ideal (𝓞 K)) ≤ 𝔭.asIdeal := by
  classical
  have := Fintype.ofFinite ι
  set m : Ideal (𝓞 K) := (∏ i, Ideal.span {((n i : ℕ) : 𝓞 K)}) * ∏ 𝔭 ∈ hS.toFinset, 𝔭.asIdeal with hm
  have hm0 : m ≠ ⊥ := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => 𝔭.ne_bot)
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn i
  obtain ⟨I, hI, hsup⟩ := GlobalTheory.exists_integral_ideal_in_class_coprime K m hm0 c
  refine ⟨I, hI, fun i => ?_, fun 𝔭 h𝔭 hle => 𝔭.isPrime.ne_top ?_⟩
  · rw [Ideal.isCoprime_iff_sup_eq, ← top_le_iff, ← hsup]
    refine sup_le_sup_left (Ideal.le_of_dvd (Dvd.dvd.mul_right ?_ _)) _
    exact Finset.dvd_prod_of_mem (fun i => Ideal.span {((n i : ℕ) : 𝓞 K)}) (Finset.mem_univ i)
  · have h : m ≤ 𝔭.asIdeal :=
      Ideal.le_of_dvd (Dvd.dvd.mul_left
        (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) (hS.mem_toFinset.mpr h𝔭)) _)
    exact top_le_iff.mp (hsup ▸ sup_le hle h)

theorem le_of_integral {A B : Formalism.L2.Host.Fld} (h : ∀ x ∈ A, IsIntegral ℤ x → x ∈ B) : A ≤ B := by
  intro x hx
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  have h1 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Qb).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨a, ha, hi⟩ := h1.exists_integral_multiple
  have h2 : a • x ∈ B := h _ (zsmul_mem hx a) hi
  have h3 : x = ((a : Qb))⁻¹ * (a • x) := by
    have : (a : Qb) ≠ 0 := by exact_mod_cast ha
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ this]
  rw [h3]
  exact mul_mem (inv_mem (intCast_mem B a)) h2

end GlobalTheory.HostDatumExists
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldTopMaximalUnramified

section

@[expose] public section

noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

theorem rayField_top_maximal_unramified : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ),
    IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M),
      (j.fieldRange ≤ qb ι M ∧
        (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ qb ι M, σ y ∈ qb ι M) ∧
        ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
          ∀ y ∈ qb ι M, σ (τ y) = τ (σ y)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L],
        (j.fieldRange ≤ L ∧ (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ L, σ y ∈ L) ∧
          ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
            ∀ y ∈ L, σ (τ y) = τ (σ y)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hst, hc, hd, hmax⟩ := hilbert_qb_aut H E j ι M hM
  have hm : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ GalOf j.fieldRange ↔ ∀ x ∈ j.fieldRange, σ x = x := fun σ =>
    IntermediateField.mem_fixingSubgroup_iff _ _
  exact ⟨hN, ⟨h, fun σ hσ => hst σ ((hm σ).2 hσ), fun σ τ hσ hτ => hc σ ((hm σ).2 hσ) τ ((hm τ).2 hτ)⟩, hd,
    fun L _ hL => hmax L hL.1 fun σ hσ τ hτ => hL.2.2 σ τ ((hm σ).1 hσ) ((hm τ).1 hτ)⟩

end GlobalTheory.HilbertInClosure

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHostDatum

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Published GlobalTheory.Mem.HD
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.HostDatumExists
theorem exists_hostDatum_alt : GlobalArtinReciprocity → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (T : _root_.Formalism.L2.TiedDataSAlt ex), HostPins D ex.nch → ∀ B : PlacesOverCommonPrime D.host, ∃ hd : _root_.Formalism.L2.HostDatumWithTies T, hd.d3b = B := by
  intro hA D L hT Gi Gl K Y cX ex T hP B
  obtain ⟨M, hM, hO⟩ := hP.hilb
  have hφ : T.host.fr.ι.comp T.host.fr.j.toRingHom = D.host.φ₀ := RingHom.ext T.host.fr.phi0
  have hE : IsTotallyComplex D.host.E := inferInstance
  obtain ⟨nf, h1, h2, h3⟩ := GlobalTheory.HilbertInClosure.rayField_top_maximal_unramified hA D.host.E T.host.fr.j T.host.fr.ι M
    (by rw [hφ]; exact hM)
  rw [T.host.fr.range] at h1 h3
  have hS : (⋃ w ∈ {w | D.what₂.muAt w ≠ D.what₂.mu0},
      (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.under (𝓞 D.host.K)) '' (ex.nch.Q w : Set (PlE D.host))).Finite :=
    hP.fin.biUnion fun w _ => (ex.nch.Q w).finite_toSet.image _
  choose rep hrep hcop hpr using exists_reps D.host.K (fun u => (D.mem u).A.T) (fun u => (D.mem u).A.T_prime.ne_zero) _ hS
  have hgal : IsGalois ℚ T.host.LLQ := by
    have := hP.gal
    exact IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField T.host.jLL.toRatAlgHom)
  refine ⟨{ d3b := B
            Tu_g := hP.Tu_g
            Qw_Tu := hP.Qw_Tu
            clsK := ⟨rep, hrep⟩
            clsK_Tu := hcop
            clsK_Qw := fun w hw v hv c => hpr c _ (Set.mem_biUnion hw ⟨v, hv, rfl⟩)
            LLgal := hgal
            HE := qb T.host.fr.ι M
            HE_fd := inferInstance
            HE_hilb := ⟨h1, h2, fun L' _ hL hU => @h3 L' {} hL hU⟩
            HE_le := le_of_integral fun x hx hi => ?_ }, rfl⟩
  obtain ⟨y, hy⟩ := hO (T.host.fr.ι x) hx (hi.map T.host.fr.ι.toIntAlgHom)
  refine ((T.what₂.O.range x).1 ⟨y, T.host.fr.ι.injective ?_⟩).1
  rw [T.host.embLL, hy]
end GlobalTheory.HostDatumExists
end
end
end

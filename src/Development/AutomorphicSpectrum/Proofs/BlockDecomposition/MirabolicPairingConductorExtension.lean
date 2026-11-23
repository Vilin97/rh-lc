module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthVanishingStatement
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
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
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesBoxMembershipStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedSmallShearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentity
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSetFiniteCosetRepresentatives

section

@[expose] public section

open scoped Topology

namespace GlobalTheory.CompanionTheory.OpenSubgroupCosets

theorem exists_finset_unique_coset_reps :
    ∀ {E : Type} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
      (D : AddSubgroup E), IsOpen (D : Set E) → ∀ (R : Set E), IsCompact R →
      ∃ S : Finset E, (∀ s ∈ S, s ∈ R) ∧ ∀ x ∈ R, ∃! s, s ∈ S ∧ x - s ∈ D := by
  intro E _ _ _ D hD R hR
  classical
  obtain ⟨t, ht⟩ := hR.elim_finite_subcover (fun x : E => (fun y => y - x) ⁻¹' (D : Set E))
    (fun x => hD.preimage (continuous_sub_right x))
    (fun r _ => Set.mem_iUnion.2 ⟨r, by simp⟩)
  set π : E → E ⧸ D := QuotientAddGroup.mk with hπ
  have hfin : (π '' R).Finite := by
    apply (t.finite_toSet.image π).subset
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨x, hx, hrx⟩ : ∃ x ∈ t, r - x ∈ D := by simpa using ht hr
    refine ⟨x, hx, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.2
    rw [← neg_sub]
    exact D.neg_mem hrx
  have hrep : ∀ c ∈ π '' R, ∃ r, r ∈ R ∧ π r = c := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩
  choose! f hfR hfπ using hrep
  refine ⟨hfin.toFinset.image f, ?_, ?_⟩
  · intro s hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
    exact hfR c (hfin.mem_toFinset.1 hc)
  · intro x hx
    have hxc : π x ∈ π '' R := ⟨x, hx, rfl⟩
    refine ⟨f (π x), ⟨Finset.mem_image.2 ⟨π x, hfin.mem_toFinset.2 hxc, rfl⟩, ?_⟩, ?_⟩
    · exact QuotientAddGroup.eq_iff_sub_mem.1 (hfπ (π x) hxc).symm
    · rintro s ⟨hs, hxs⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
      have hc' := hfin.mem_toFinset.1 hc
      have h1 : π x = c := by
        rw [← hfπ c hc']
        exact QuotientAddGroup.eq_iff_sub_mem.2 hxs
      rw [h1]

end GlobalTheory.CompanionTheory.OpenSubgroupCosets
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelNonvanishing

section

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.AvgBox

theorem setIntegral_eq_sum_reps {E : Type} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    (μ : Measure E) [μ.IsAddLeftInvariant] (D M : AddSubgroup E) (hD : MeasurableSet (D : Set E))
    (hfin : μ (D : Set E) ≠ ⊤) (hDM : D ≤ M) (S : Finset E) (hSM : ∀ s ∈ S, s ∈ M)
    (hS : ∀ x ∈ M, ∃! s, s ∈ S ∧ x - s ∈ D) (f : E → ℂ) (hf : ∀ x, ∀ d ∈ D, f (x + d) = f x) :
    ∫ x in (M : Set E), f x ∂μ = ((μ.real (D : Set E) : ℝ) : ℂ) * ∑ s ∈ S, f s := by
  classical
  set A : E → Set E := fun s => (fun x => -s + x) ⁻¹' (D : Set E) with hA
  have hAm : ∀ s, MeasurableSet (A s) := fun s => (measurable_const_add (-s)) hD
  have hmem : ∀ s x, x ∈ A s ↔ x - s ∈ D := by
    intro s x
    simp only [hA, Set.mem_preimage, SetLike.mem_coe, neg_add_eq_sub]
  have hAM : ∀ s ∈ S, ∀ x ∈ A s, x ∈ M := by
    intro s hs x hx
    have := M.add_mem (hDM ((hmem s x).1 hx)) (hSM s hs)
    simpa using this
  have hU : (M : Set E) = ⋃ s ∈ S, A s := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    constructor
    · intro hx
      obtain ⟨s, ⟨hs, hxs⟩, -⟩ := hS x hx
      exact ⟨s, hs, (hmem s x).2 hxs⟩
    · rintro ⟨s, hs, hx⟩
      exact hAM s hs x hx
  have hdisj : Set.Pairwise (S : Set E) (Function.onFun Disjoint A) := by
    intro s hs s' hs' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    exact (hS x (hAM s hs x hx)).unique ⟨hs, (hmem s x).1 hx⟩ ⟨hs', (hmem s' x).1 hx'⟩
  have hconst : ∀ s, Set.EqOn (fun _ => f s) f (A s) := by
    intro s x hx
    have := hf s (x - s) ((hmem s x).1 hx)
    simpa using this.symm
  have hvol : ∀ s, μ (A s) = μ (D : Set E) := fun s => measure_preimage_add μ (-s) _
  rw [hU, integral_biUnion_finset S (fun s _ => hAm s) hdisj ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← setIntegral_congr_fun (hAm s) (hconst s), setIntegral_const]
    simp [Measure.real, hvol]
  · intro s _
    refine IntegrableOn.congr_fun ?_ (hconst s) (hAm s)
    exact integrableOn_const (by rw [hvol]; exact hfin)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem uM_add (n : ℕ) (x y : Fin n → k) : uM n (x + y) = uM n x * uM n y := by
  simp only [uM, ofAdd_add, map_mul]

theorem continuous_uM (n : ℕ) : Continuous (uM (k := k) n) :=
  (continuous_unipIn n).comp continuous_ofAdd

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem sub_smul_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (y : Fin (n + 1) → k) (v : V) :
    T (uM (n + 1) y) v - ((ψ (y (Fin.last n)) : Circle) : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  let x : MirUin k (n + 1) := ⟨uM (n + 1) y, Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd y, rfl⟩⟩
  have hx := mirChar_eq k ψ n x (Multiplicative.ofAdd y) rfl
  refine Submodule.subset_span ⟨x, v, ?_⟩
  rw [hx]
  rfl

theorem wt_mul_psi (ψ : AddChar k Circle) (y : Fin (n + 1) → k) :
    wt ψ n y * ((ψ (y (Fin.last n)) : Circle) : ℂ) = 1 := by
  rw [wt, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  simp

theorem avg_sub_mem_twKer (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (S : Finset (Fin (n + 1) → k)) (v : V) :
    (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v ∈
      twKer T (MirUin k (n + 1)) (mirChar k ψ n) := by
  have h : (∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v) - (S.card : ℂ) • v =
      ∑ s ∈ S, wt ψ n s • (T (uM (n + 1) s) v - ((ψ (s (Fin.last n)) : Circle) : ℂ) • v) := by
    simp only [smul_sub, smul_smul, wt_mul_psi, one_smul, Finset.sum_sub_distrib, Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (sub_smul_mem_twKer ψ T s v)

theorem integrand_add (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (v : V) (v' : V') (x d : Fin (n + 1) → k) (hd : T (uM (n + 1) d) v = v)
    (hψ : ψ (d (Fin.last n)) = 1) :
    wt ψ n (x + d) * coef T B v v' (x + d) = wt ψ n x * coef T B v v' x := by
  have h1 : wt ψ n (x + d) = wt ψ n x := by
    simp only [wt, Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, hψ, inv_one, mul_one]
  have h2 : coef T B v v' (x + d) = coef T B v v' x := by
    simp only [coef, uM_add, map_mul, Module.End.mul_apply, hd]
  rw [h1, h2]

end Rep

theorem exists_JJ_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → ∃ v', JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT hB v hv
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  haveI : (piHaar ν (n + 1)).IsAddHaarMeasure := by
    unfold piHaar
    infer_instance
  obtain ⟨r, hr⟩ := exists_cball_addChar_eq_one ψ hψ
  have hΩ₁ : {y : Fin (n + 1) → k | T (uM (n + 1) y) v = v} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    refine ((hT v).preimage (continuous_uM (n + 1))).mem_nhds ?_
    simp [uM]
  have hΩ₂ : {y : Fin (n + 1) → k | y (Fin.last n) ∈ cball r} ∈ 𝓝 (0 : Fin (n + 1) → k) := by
    have h0 : cball r ∈ 𝓝 ((0 : Fin (n + 1) → k) (Fin.last n)) := by simpa using cball_mem_nhds r
    exact (continuous_apply (Fin.last n)).continuousAt h0
  obtain ⟨t₀, ht₀⟩ := exists_box_subset (Filter.inter_mem hΩ₁ hΩ₂)
  refine ⟨t₀, fun t ht => ?_⟩
  have hDM : box (n + 1) t₀ ≤ box (n + 1) t := fun x hx j =>
    show valuation k (x j) ≤ valuation k (t : k) from
      le_trans (show valuation k (x j) ≤ valuation k (t₀ : k) from hx j) ht
  have hDo : IsOpen (box (n + 1) t₀ : Set (Fin (n + 1) → k)) :=
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (box_mem_nhds (n + 1) t₀)
  obtain ⟨S, hSM, hS⟩ := GlobalTheory.CompanionTheory.OpenSubgroupCosets.exists_finset_unique_coset_reps
    (box (n + 1) t₀) hDo (box (n + 1) t : Set (Fin (n + 1) → k)) (isCompact_box (n + 1) t)
  have hfin : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ ⊤ :=
    (isCompact_box (n + 1) t₀).measure_lt_top.ne
  have hpos : piHaar ν (n + 1) (box (n + 1) t₀ : Set (Fin (n + 1) → k)) ≠ 0 :=
    hDo.measure_ne_zero _ ⟨0, (box (n + 1) t₀).zero_mem⟩
  have hvol : ((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) ≠ 0 :=
    (ENNReal.toReal_pos hpos hfin).ne'
  have hcard : (S.card : ℂ) ≠ 0 := by
    obtain ⟨s, ⟨hs, -⟩, -⟩ := hS 0 (box (n + 1) t).zero_mem
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hs)
  set v₁ : V := ∑ s ∈ S, wt ψ n s • T (uM (n + 1) s) v with hv₁
  have hv₁0 : v₁ ≠ 0 := by
    intro h0
    have h := avg_sub_mem_twKer ψ T S v
    rw [← hv₁, h0, zero_sub, neg_mem_iff] at h
    exact hv ((Submodule.smul_mem_iff _ hcard).1 h)
  obtain ⟨v', hv'⟩ := hB v₁ hv₁0
  refine ⟨v', ?_⟩
  have hJ : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' =
      (((piHaar ν (n + 1)).real (box (n + 1) t₀ : Set (Fin (n + 1) → k)) : ℝ) : ℂ) * B v₁ v' := by
    rw [JJ, setIntegral_eq_sum_reps (piHaar ν (n + 1)) (box (n + 1) t₀) (box (n + 1) t) hDo.measurableSet hfin hDM S
      hSM hS _ fun x d hd => integrand_add ψ T B v v' x d (ht₀ hd).1 (hr _ (ht₀ hd).2)]

    simp only [hv₁, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, coef]
  rw [hJ]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 hvol) hv'

end GlobalTheory.CompanionTheory.MirPair.AvgBox

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelNonvanishingStatement

section

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_twisted_kernel_nonvanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → ∃ v', JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.AvgBox.exists_JJ_ne_zero | exact GlobalTheory.CompanionTheory.MirPair.AvgBox.exists_JJ_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MirPair.AvgBox.exists_JJ_ne_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFiniteStatement

section

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.shear_orbit_box_finite_of_isSmooth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V), IsSmooth T → ∀ (v : V) (r : kˣ), valuation k (r : k) < 1 → ((fun b => T (levi k (n + 1) (shearGL n b)) v) '' (box (n + 1) r : Set (Fin (n + 1) → k))).Finite := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite | exact GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite | (intros; apply GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtension

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Nondeg

theorem box_subset_of_valuation_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {m : ℕ} {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) :
    (box m s : Set (Fin m → k)) ⊆ box m t := fun x hx j =>
  le_trans (show valuation k (x j) ≤ valuation k (s : k) from hx j) h

theorem exists_unit_bound {k : Type} [Field k] [ValuativeRel k] {W : Type} {S : Set W} (hS : S.Finite)
    (τ : W → kˣ) (t : kˣ) :
    ∃ u : kˣ, valuation k (t : k) ≤ valuation k (u : k) ∧
      ∀ w ∈ S, valuation k (τ w : k) ≤ valuation k (u : k) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨t, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨u, h1, h2⟩ := ih
    rcases le_total (valuation k (u : k)) (valuation k (τ a : k)) with h | h
    · refine ⟨τ a, h1.trans h, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact le_rfl
      · exact (h2 w hw).trans h
    · refine ⟨u, h1, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact h
      · exact h2 w hw

theorem exists_large_unit {k : Type} [Field k] [ValuativeRel k] (c r t₀ : kˣ) :
    ∃ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) ∧
      valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
  · refine ⟨c * r⁻¹, h, ?_⟩
    have e : c * (c * r⁻¹)⁻¹ = r := by simp
    rw [e]
  · refine ⟨t₀, le_rfl, ?_⟩
    have e : ((c * t₀⁻¹ : kˣ) : k) = ((c * r⁻¹ : kˣ) : k) * ((t₀⁻¹ : kˣ) : k) * (r : k) := by
      push_cast
      field_simp
    have e1 : valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) = 1 := by
      rw [← map_mul]
      simp
    rw [e, map_mul, map_mul]
    calc valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k)
        ≤ valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k) := by gcongr
      _ = valuation k (r : k) := by rw [e1, one_mul]

theorem continuous_wt_mul_coef {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) {n : ℕ} {V V' : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hT : IsSmooth T) (v : V) (v' : V') :
    Continuous fun x => wt ψ n x * coef T B v v' x := by
  refine Continuous.mul ?_ (continuous_coef T B hT v v')
  have h : Continuous fun x : Fin (n + 1) → k => ψ (-x (Fin.last n)) :=
    hψ.comp (continuous_apply _).neg
  exact continuous_subtype_val.comp h

end GlobalTheory.CompanionTheory.MirPair.Nondeg

namespace GlobalTheory.CompanionTheory.MirPair


open GlobalTheory.CompanionTheory.MirPair.Nondeg in
theorem exists_evVal_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ (v' : V') (A : ℂ), EvVal ν ψ T B v v' A ∧ A ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hinv hnd v hv
  obtain ⟨r₁, hr₁, hfix⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₂, hr₂, hlat⟩ := GlobalTheory.T.shear_preserves_box_membership (k := k) (n := n) 1
  obtain ⟨r, hr, hrr₁, hrr₂⟩ : ∃ r : kˣ, valuation k (r : k) < 1 ∧
      valuation k (r : k) ≤ valuation k (r₁ : k) ∧ valuation k (r : k) ≤ valuation k (r₂ : k) := by
    rcases le_total (valuation k (r₁ : k)) (valuation k (r₂ : k)) with h | h
    · exact ⟨r₁, hr₁, le_rfl, h⟩
    · exact ⟨r₂, hr₂, h, le_rfl⟩
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.mirabolic_twisted_kernel_nonvanishing ν ψ T B hψ hT hnd v hv
  obtain ⟨t, htt₀, htc⟩ := exists_large_unit c r t₀
  obtain ⟨v', hv'⟩ := ht₀ t htt₀
  by_contra hno
  push_neg at hno
  have hev : ∀ w : V', ∃ τ : kˣ, ∀ u : kˣ, valuation k (τ : k) ≤ valuation k (u : k) →
      JJ ν ψ T B (box (n + 1) u : Set (Fin (n + 1) → k)) v w = 0 := by
    intro w
    obtain ⟨A, hA⟩ := GlobalTheory.T.mirabolic_pairing_exists_eventual_value ν ψ c T T' B s hψ hc hT hT' hinv v w
    have h0 : A = 0 := hno w A hA
    obtain ⟨τ, hτ⟩ := hA
    exact ⟨τ, fun u hu => (hτ u hu).trans h0⟩
  choose τ hτ using hev
  obtain ⟨u, htu, hu⟩ := exists_unit_bound (GlobalTheory.T.shear_orbit_box_finite_of_isSmooth T' hT' v' r hr) τ t
  have hz : ∀ b ∈ box (n + 1) (c * t⁻¹), ∫ x in (box (n + 1) u : Set (Fin (n + 1) → k)),
      ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = 0 := by
    intro b hb
    have hbr : b ∈ (box (n + 1) r : Set (Fin (n + 1) → k)) := box_subset_of_valuation_le htc hb
    have hlast : valuation k (b (Fin.last n)) < 1 :=
      lt_of_le_of_lt (show valuation k (b (Fin.last n)) ≤ valuation k (r : k) from hbr _) hr
    rw [GlobalTheory.T.mirabolic_pairing_depth_vanishing ν ψ T T' B s hψ hT hinv b _ v v' hlast
      (hfix b (box_subset_of_valuation_le hrr₁ hbr)) ?_]
    · exact hτ _ u (hu _ ⟨b, hbr, rfl⟩)
    · intro x
      have h := hlat b (box_subset_of_valuation_le hrr₂ hbr) u x
      simpa using h
  have hm : MeasurableSet (box (n + 1) u : Set (Fin (n + 1) → k)) := by
    rw [coe_box]
    exact MeasurableSet.univ_pi fun _ => (isOpen_cball u).measurableSet
  have hfin := setIntegral_inter_box_of_twists ν ψ c hψ hc (n + 1) t
    (box (n + 1) u : Set (Fin (n + 1) → k)) (fun x => wt ψ n x * coef T B v v' x) 0
    (isCompact_box _ _) hm (continuous_wt_mul_coef ψ hψ T B hT v v') hz
  rw [Set.inter_eq_right.2 (box_subset_of_valuation_le htu)] at hfin
  exact hv' hfin

end GlobalTheory.CompanionTheory.MirPair

end
end
end

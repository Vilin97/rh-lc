module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Mathlib.NumberTheory.NumberField.Basic
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.HLatOps
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.StExtInv
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.HnStepEqOfNorm

section

@[expose] public section

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

section ExtensionInterSubspace

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_compl_inf (L : Submodule (𝓞 K) V) (hL : L.FG) (W₀ : Submodule K V) :
    ∃ C : Submodule (𝓞 K) V, C ≤ L ∧
      (∀ x ∈ L, ∃ a ∈ L ⊓ W₀.restrictScalars (𝓞 K), ∃ c ∈ C, x = a + c) ∧
      ∀ u ∈ Submodule.span K (C : Set V), u ∈ W₀ → u = 0 := by
  classical
  let N : Submodule (𝓞 K) L := (W₀.restrictScalars (𝓞 K)).comap L.subtype
  have htor : Submodule.torsion (𝓞 K) (L ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, haq⟩ := (Submodule.mem_torsion_iff q).1 hq
    obtain ⟨z, rfl⟩ := N.mkQ_surjective q
    have h1 : ((a : 𝓞 K) • z) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submonoid.smul_def] using haq
    have ha0 : algebraMap (𝓞 K) K (a : 𝓞 K) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have h2 : (z : V) ∈ W₀ := by
      have h3 : ((a : 𝓞 K) • (z : V)) ∈ W₀ := h1
      rw [← algebraMap_smul K] at h3
      have h4 := W₀.smul_mem (algebraMap (𝓞 K) K a)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h4
    rw [Submodule.mem_bot]
    exact (Submodule.Quotient.mk_eq_zero N).2 h2
  have : Module.Flat (𝓞 K) (L ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have := Module.finitePresentation_of_finite (𝓞 K) (L ⧸ N)
  have : Module.Projective (𝓞 K) (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' : ∀ q, N.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  refine ⟨(LinearMap.range s).map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.2
  · intro x hx
    have hmem : ((⟨x, hx⟩ : L) - s (N.mkQ ⟨x, hx⟩)) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      have := hs' (N.mkQ ⟨x, hx⟩)
      simp only [Submodule.mkQ_apply] at this ⊢
      rw [this, sub_self]
    refine ⟨x - (s (N.mkQ ⟨x, hx⟩) : V), ⟨L.sub_mem hx (s _).2, hmem⟩,
      (s (N.mkQ ⟨x, hx⟩) : V), ⟨s (N.mkQ ⟨x, hx⟩), ⟨_, rfl⟩, rfl⟩, by abel⟩
  · intro u hu huW
    obtain ⟨d, hd, hdu⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS _ hu
    obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hdu
    have hW : ((s q : L) : V) ∈ W₀ := by
      rw [show ((s q : L) : V) = d • u from hq, ← algebraMap_smul K d u]
      exact W₀.smul_mem _ huW
    have hq0 : q = 0 := by
      rw [← hs' q]
      exact (Submodule.Quotient.mk_eq_zero N).2 hW
    have h5 : d • u = 0 := by
      rw [← hq, hq0, map_zero, map_zero]
    rw [← algebraMap_smul K d u] at h5
    exact (smul_eq_zero.1 h5).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)

end ExtensionInterSubspace

section Transport

variable {R : Type*} [Ring R] {V : Type*} [AddCommGroup V] [Module R V]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end Transport

end Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedSpanEigenVectorMemEigenSublattice

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.EigenSpanSat

def eigenSub {K : Type} [Field K] {n : ℕ} {O : Type} (r : O → Matrix (Fin n) (Fin n) K)
    (τ : O → K) : Submodule K (Fin n → K) where
  carrier := {c | ∀ a, (r a).mulVec c = τ a • c}
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [Matrix.mulVec_add, hx a, hy a, smul_add]
  zero_mem' := by
    intro a
    simp
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Matrix.mulVec_smul, hx a, smul_comm]

theorem map_mulVec {K L : Type} [Field K] [Field L] (iK : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    (M.map iK).mulVec (fun i => iK (c i)) = fun i => iK (M.mulVec c i) := by
  funext i

  simp [Matrix.mulVec, dotProduct, map_sum]

theorem eq_zero_of_eigen {K L : Type} [Field K] [Field L] (iK : K →+* L) {n : ℕ} {O : Type}
    (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) {m : ℕ} (σ : Fin m → L)
    (c : Fin m → (Fin n → K))
    (hP : ∀ d : Fin m → K, (∀ a, (r a).mulVec (∑ i, d i • c i) = τ a • ∑ i, d i • c i) →
      ∑ i, d i • c i = 0)
    (he : ∀ a, ((r a).map iK).mulVec (∑ i, σ i • fun t => iK (c i t)) =
      iK (τ a) • ∑ i, σ i • fun t => iK (c i t)) :
    ∑ i, σ i • (fun t => iK (c i t)) = 0 := by
  let _ : Algebra K L := iK.toAlgebra
  let S := Submodule.span K (Set.range σ)
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range σ)
  let b := Module.finBasis K S
  have hli : LinearIndependent K (fun k => (b k : L)) :=
    b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let D : Fin (finrank K S) → Fin m → K :=
    fun k i => b.repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩ k
  have hσ : ∀ i, σ i = ∑ k, iK (D k i) * (b k : L) := by
    intro i
    have h := congrArg Subtype.val (b.sum_repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩)
    refine h.symm.trans ?_
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Algebra.smul_def]
    rfl

  have hvan : ∀ v : Fin (finrank K S) → (Fin n → K),
      (∑ k, (b k : L) • fun t => iK (v k t)) = 0 → ∀ k, v k = 0 := by
    intro v hv k
    funext t
    have h := congrFun hv t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have := Fintype.linearIndependent_iff.1 hli (fun k => v k t) (by
      rw [← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, mul_comm]
      rfl)
    exact this k
  let u : Fin (finrank K S) → (Fin n → K) := fun k => ∑ i, D k i • c i
  have hy : (∑ i, σ i • (fun t => iK (c i t))) = ∑ k, (b k : L) • fun t => iK (u k t) := by
    funext t

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u, map_sum, map_mul, hσ,
    Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hu : ∀ k, u k = 0 := by
    intro k
    apply hP
    intro a
    have h1 := hvan (fun k => (r a).mulVec (u k) - τ a • u k) (by
      have h2 := he a
      rw [hy, Matrix.mulVec_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_smul, map_mulVec, smul_comm (iK (τ a)), ← smul_sub]
      congr 1
      funext t
      simp [map_sub, map_mul])
    exact sub_eq_zero.1 (h1 k)
  rw [hy]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hu k]
  funext t
  simp

end GlobalTheory.EigenSpanSat

namespace GlobalTheory.EigenSpanSat

theorem span_eigen_sat : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (O : Type) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : Formalism.L2.Pj.CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → Λ.FG → ∀ x : Fin n → T.Fr, x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' (Λ : Set (Fin n → K))) → (∀ a, ((r a).map iK).mulVec x = iK (τ a) • x) → x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) := by
  intro K _ _ n Λ O r τ 𝔓 T iK _ hFG x hx he
  obtain ⟨C, -, hdec, hCW⟩ :=
    Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd.exists_compl_inf Λ hFG (eigenSub r τ)
  obtain ⟨m, s, g, hg⟩ := Submodule.mem_span_set'.1 hx
  choose l hl hlg using fun i => (g i).2
  choose p hp q hq hpq using fun i => hdec (l i) (hl i)
  let σ : Fin m → T.Fr := fun i => algebraMap T.V T.Fr (s i)
  have hsplit : x = ∑ i, σ i • (fun t => iK (p i t)) + ∑ i, σ i • (fun t => iK (q i t)) := by
    rw [← hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hlg i, hpq i, ← smul_add, algebraMap_smul]
    congr 1
    funext t
    simp
  have hpE : ∀ i a, (r a).mulVec (p i) = τ a • p i := fun i => (hp i).2
  have hx1 : ∀ a, ((r a).map iK).mulVec (∑ i, σ i • fun t => iK (p i t)) =
      iK (τ a) • ∑ i, σ i • fun t => iK (p i t) := by
    intro a
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, map_mulVec, hpE i a, smul_comm]
    congr 1
    funext t
    simp
  have hx2 : ∑ i, σ i • (fun t => iK (q i t)) = 0 := by
    refine eq_zero_of_eigen iK r τ σ q (fun d hd => ?_) (fun a => ?_)
    · refine hCW _ (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (hq i))) hd
    · have h := he a
      rw [hsplit, Matrix.mulVec_add, hx1 a, smul_add] at h
      exact add_left_cancel h
  rw [hsplit, hx2, add_zero]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p i, ⟨(hp i).1, (hp i).2⟩, rfl⟩)

end GlobalTheory.EigenSpanSat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedSpanEigenVectorMemEigenSublatticeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem _root_.GlobalTheory.T.completed_span_eigen_vector_mem_eigen_sublattice : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (O : Type) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : Formalism.L2.Pj.CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → Λ.FG → ∀ x : Fin n → T.Fr, x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' (Λ : Set (Fin n → K))) → (∀ a, ((r a).map iK).mulVec x = iK (τ a) • x) → x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) := by
  first | exact @GlobalTheory.EigenSpanSat.span_eigen_sat | exact GlobalTheory.EigenSpanSat.span_eigen_sat | (intros; apply GlobalTheory.EigenSpanSat.span_eigen_sat <;> assumption)
end
end

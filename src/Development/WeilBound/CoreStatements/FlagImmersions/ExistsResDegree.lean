module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexed
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsMultiHomogIdealMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import Development.WeilBound.CoreStatements.FlagImmersions.BirationalOfClosure
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullback
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAnResNullForm
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.InteriorUnionEmpty

section

@[expose] public section

noncomputable section

namespace RootFieldNumerics.Ref.Comp

open ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.PB Topology Filter

theorem analytic_union {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {S T : Set X}
    (hS : A.IsAnalyticSubset S) (hT : A.IsAnalyticSubset T) : A.IsAnalyticSubset (S ∪ T) := by
  intro x
  obtain ⟨W, hW, hx, r, f, hf, hSW⟩ := hS x
  obtain ⟨W', hW', hx', r', f', hf', hTW⟩ := hT x
  refine ⟨W ∩ W', hW.inter hW', ⟨hx, hx'⟩, r * r', fun i y => f (finProdFinEquiv.symm i).1 y *
    f' (finProdFinEquiv.symm i).2 y, fun i j t ht => ?_, ?_⟩
  · exact (hf _ j t ⟨ht.1, ht.2.1⟩).mul (hf' _ j t ⟨ht.1, ht.2.2⟩)
  · ext y
    have h1 := Set.ext_iff.1 hSW y
    have h2 := Set.ext_iff.1 hTW y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union] at h1 h2 ⊢
    constructor
    · rintro ⟨h | h, hy⟩
      · exact ⟨hy, fun i => by rw [(h1.1 ⟨h, hy.1⟩).2, zero_mul]⟩
      · exact ⟨hy, fun i => by rw [(h2.1 ⟨h, hy.2⟩).2, mul_zero]⟩
    · rintro ⟨hy, h⟩
      refine ⟨?_, hy⟩
      by_contra hn
      push Not at hn
      have a1 : ∃ i, f i y ≠ 0 := by
        by_contra h3
        push Not at h3
        exact hn.1 (h1.2 ⟨hy.1, h3⟩).1
      have a2 : ∃ i, f' i y ≠ 0 := by
        by_contra h3
        push Not at h3
        exact hn.2 (h2.2 ⟨hy.2, h3⟩).1
      obtain ⟨i, hi⟩ := a1
      obtain ⟨i', hi'⟩ := a2
      have := h (finProdFinEquiv (i, i'))
      simp only [Equiv.symm_apply_apply] at this
      exact mul_ne_zero hi hi' this

theorem interior_union_empty {X : Type} [TopologicalSpace X] {S T : Set X} (hS : IsClosed S) (h1 : interior S = ∅)
    (h2 : interior T = ∅) : interior (S ∪ T) = ∅ := by
  rw [interior_union_isClosed_of_interior_empty hS h2, h1]

theorem interior_preimage {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] [CompactSpace Z]
    {h : Z → Y} (hh : Continuous h) {N T : Set Y} (hN : IsClosed N) (hNi : interior (h ⁻¹' N) = ∅)
    (hfib : ∀ x ∉ N, (h ⁻¹' {x}).ncard = 1) (hT : interior T = ∅) : interior (h ⁻¹' T) = ∅ := by
  by_contra hne
  have hd : Dense (h ⁻¹' N)ᶜ := interior_eq_empty_iff_dense_compl.1 hNi
  obtain ⟨z, hzN, hzO⟩ := hd.exists_mem_open isOpen_interior (Set.nonempty_iff_ne_empty.2 hne)
  have hC : IsClosed (h '' (interior (h ⁻¹' T))ᶜ) :=
    (isOpen_interior.isClosed_compl.isCompact.image hh).isClosed
  have hO : IsOpen ((h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ) := hC.isOpen_compl.inter hN.isOpen_compl
  have hsub : (h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ ⊆ T := by
    rintro x ⟨h1, h2⟩
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hfib x h2)
    have hcx : h c = x := by
      have : c ∈ h ⁻¹' {x} := by rw [hc]; rfl
      exact this
    have : c ∈ interior (h ⁻¹' T) := by
      by_contra hn
      exact h1 ⟨c, hn, hcx⟩
    have h3 : c ∈ h ⁻¹' T := interior_subset this
    rw [← hcx]
    exact h3
  have hmem : h z ∈ (h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ := by
    refine ⟨?_, hzN⟩
    rintro ⟨w, hw, hwz⟩
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hfib (h z) hzN)
    have e1 : w ∈ h ⁻¹' {h z} := hwz
    have e2 : z ∈ h ⁻¹' {h z} := rfl
    rw [hc] at e1 e2
    exact hw ((e1.trans e2.symm) ▸ hzO)
  have := interior_maximal hsub hO hmem
  rw [hT] at this
  exact this

theorem degree_comp {e d : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace Z] [CompactSpace Z] {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {C : FinHolAtlas e Z}
    {π : Y → X} {h : Z → Y} {br S : Set X} {N : Set Y} (hπ : HoloMap B A π) (hh : HoloMap C B h) (hd : 0 < d)
    (hdπ : IsDegreeOff A B π d br) (hdh : IsDegreeOff B C h 1 N) (hS : A.IsAnalyticSubset S)
    (hSi : interior (π ⁻¹' S) = ∅) (hNS : N ⊆ π ⁻¹' S) : IsDegreeOff A C (π ∘ h) d (br ∪ S) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hdπ
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hdh
  have hcomp := CovMap.holoMap_comp hh hπ
  have hbrc : IsClosed br := isClosed_of_isAnalyticSubset A a1
  have hSi' : interior S = ∅ := by
    by_contra hne
    have hdn : Dense brᶜ := interior_eq_empty_iff_dense_compl.1 a2
    obtain ⟨x, hx, hxO⟩ := hdn.exists_mem_open isOpen_interior (Set.nonempty_iff_ne_empty.2 hne)
    have hpos : 0 < (π ⁻¹' {x}).ncard := by rw [a5 x hx]; exact hd
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    have hy' : π y = x := hy
    have : y ∈ interior (π ⁻¹' S) := preimage_interior_subset_interior_preimage hπ.1 (by
      show π y ∈ interior S
      rw [hy']; exact hxO)
    rw [hSi] at this
    exact this
  have hU := analytic_union a1 hS
  refine ⟨hU, interior_union_empty hbrc a2 hSi', CovMap.Deg.isAnalyticSubset_preimage hcomp hU, ?_, ?_, ?_⟩
  · rw [Set.preimage_comp]
    refine interior_preimage hh.1 (isClosed_of_isAnalyticSubset B b1) b4 b5 ?_
    rw [Set.preimage_union]
    exact interior_union_empty (hbrc.preimage hπ.1) a4 hSi
  · intro x hx
    have hx1 : x ∉ br := fun h => hx (Or.inl h)
    have hx2 : x ∉ S := fun h => hx (Or.inr h)
    have hN : ∀ y, π y = x → y ∉ N := fun y hy hn => hx2 (hy ▸ hNS hn)
    rw [← a5 x hx1]
    have himg : h '' ((π ∘ h) ⁻¹' {x}) = π ⁻¹' {x} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (b5 y (hN y hy))
        have hcx : h c = y := by
          have : c ∈ h ⁻¹' {y} := by rw [hc]; rfl
          exact this
        refine ⟨c, ?_, hcx⟩
        show π (h c) = x
        rw [hcx]; exact hy
    rw [← himg]
    refine (Set.InjOn.ncard_image ?_).symm
    intro z hz w _ hzw
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (b5 (h z) (hN _ hz))
    have e1 : w ∈ h ⁻¹' {h z} := hzw.symm
    have e2 : z ∈ h ⁻¹' {h z} := rfl
    rw [hc] at e1 e2
    exact e2.trans e1.symm
  · intro j k y hy hnot hk
    have hnot1 : (C.chart j).symm y ∉ h ⁻¹' N := fun hn => hnot (Or.inr (hNS hn))
    have hnot2 : h ((C.chart j).symm y) ∉ π ⁻¹' br := fun hn => hnot (Or.inl hn)
    obtain ⟨l, hl⟩ := B.cover (h ((C.chart j).symm y))
    obtain ⟨Q, hQdef⟩ : ∃ Q : (Fin e → ℂ) → Fin e → ℂ, Q = B.chart l ∘ h ∘ (C.chart j).symm :=
      ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P : (Fin e → ℂ) → Fin e → ℂ, P = A.chart k ∘ π ∘ (B.chart l).symm :=
      ⟨_, rfl⟩
    have hQa : AnalyticAt ℂ Q y := by
      rw [hQdef]
      exact hh.2 j l y ⟨hy, hl⟩
    have hu : (B.chart l).symm (Q y) = h ((C.chart j).symm y) := by
      rw [hQdef]
      exact (B.chart l).left_inv hl
    have hQt : Q y ∈ (B.chart l).target := by
      rw [hQdef]
      exact (B.chart l).map_source hl
    have hk' : π ((B.chart l).symm (Q y)) ∈ (A.chart k).source := by
      rw [hu]
      exact hk
    have hPa : AnalyticAt ℂ P (Q y) := by
      rw [hPdef]
      exact hπ.2 l k _ ⟨hQt, hk'⟩
    have hc : ContinuousAt (h ∘ (C.chart j).symm) y :=
      hh.1.continuousAt.comp ((C.chart j).continuousAt_symm hy)
    have heq : (A.chart k ∘ (π ∘ h) ∘ (C.chart j).symm) =ᶠ[nhds y] P ∘ Q := by
      filter_upwards [hc ((B.chart l).open_source.mem_nhds hl)] with t ht
      have ht' : h ((C.chart j).symm t) ∈ (B.chart l).source := ht
      rw [hPdef, hQdef]
      simp only [Function.comp, (B.chart l).left_inv ht']
    have hcomp' : fderiv ℂ (P ∘ Q) y = (fderiv ℂ P (Q y)).comp (fderiv ℂ Q y) :=
      fderiv_comp y hPa.differentiableAt hQa.differentiableAt
    rw [heq.fderiv_eq, hcomp']
    change LinearMap.det ((fderiv ℂ P (Q y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ∘ₗ
      (fderiv ℂ Q y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≠ 0
    rw [LinearMap.det_comp]
    refine mul_ne_zero ?_ ?_
    · rw [hPdef]
      exact a6 l k _ hQt (by rw [hu]; exact hnot2) hk'
    · rw [hQdef]
      exact b6 j l y hy hnot1 hl

end RootFieldNumerics.Ref.Comp
end
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.ExistsResDegree

section

@[expose] public section

noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.Ar.Chg GlobalTheory.CompanionTheory.Ar.Chg.DegBlock GroundTheory.Heights₂.Heights

private theorem not_mem_mCoordIdeal_of_aeval_ne_zero {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (G : MRing ι) (h : aeval y G ≠ 0) : G ∉ mCoordIdeal y := by
  intro hG
  apply h
  have hk : mConeMap y G = 0 := hG
  have e : ((MvPolynomial.aeval (R := Ω) (fun _ : K => (1 : Ω))).restrictScalars ℤ).comp (mConeMap y) = aeval y := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap]
  have := congrArg (fun f => f G) e
  simp only [AlgHom.comp_apply] at this
  rw [← this, hk, map_zero]

private theorem sameOrbit_comp_blkV {K₀ K : Type} {ι₀ : K₀ → Type} {ι : K → Type} (κ : K₀ → K)
    (bx : ∀ k, ι₀ k ≃ ι (κ k)) {z z₁ : (Σ k, ι k) → ℂ} (h : SameOrbit z₁ z) :
    SameOrbit (fun p => z₁ (blkV κ bx p)) (fun p => z (blkV κ bx p)) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (κ k), fun k => hc _, by funext p; rfl⟩

theorem exists_res_degree (hRes : ResExistsStatement) {K₀ K : Type} [Fintype K₀] [Fintype K] {ι₀ : K₀ → Type}
    {ι : K → Type} [∀ k, Fintype (ι₀ k)] [∀ k, Fintype (ι k)] {Ω Ωf : Type} [Field Ω] [Field Ωf] [CharZero Ω]
    (y₀ : (Σ k, ι₀ k) → Ω) (y : (Σ k, ι k) → Ω) {κ : K₀ → K} {v : (Σ k, ι₀ k) → Σ k, ι k} (hv : IsBlockMap κ v)
    (hy : ∀ p, y (v p) = y₀ p) {D : ℕ} (hA₀ : IsArithVar (mCoordIdeal y₀) (D + 1))
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hB₀ : Birational y₀) (hB : Birational y)
    {J₀ : Ideal (MRing ι₀)} (hJ : J₀ = ⊤) (R₀ : AnLogRes (mCoordIdeal y₀) J₀ D)
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R₀.X → X)
    (hπ : HoloMap R₀.A A π) {d : ℕ} (hd : 0 < d) {br : Set X} (hdeg : IsDegreeOff A R₀.A π d br)
    {n : ℕ} (yf : Fin (n + 1) → Ωf)
    (hgen : Subfield.closure (Set.range fun ij : Fin (n + 1) × Fin (n + 1) => yf ij.1 / yf ij.2) = ⊤)
    (g : Ωf →+* Ω) (hfin : letI := g.toAlgebra; 0 < Module.finrank Ωf Ω)
    (k₀ : K₀) (ix : Fin (n + 1) ≃ ι₀ k₀) (hyf : ∀ j, y₀ ⟨k₀, ix j⟩ = g (yf j))
    (pt : X → Fin (n + 1) → ℂ)
    (hpt : ∀ x, ∃ a : ℂ, (fun j => R₀.lift x x ⟨k₀, ix j⟩) = a • pt (π x))
    (hloc : ∀ x : X, ∃ (U : Set X) (lam : X → Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      (∀ j, A.HoloOn U fun y => lam y j) ∧ ∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • pt y) :
    ∃ (J : Ideal (MRing ι)) (R : AnLogRes (mCoordIdeal y) J D) (h : R.X → R₀.X) (br' : Set X),
      HoloMap R.A R₀.A h ∧ (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) ∧
      HoloMap R.A A (π ∘ h) ∧ IsDegreeOff A R.A (π ∘ h) d br' := by
  classical
  obtain ⟨bx, rfl⟩ := RootFieldNumerics.Ref.Zeros.exists_blkV hv
  subst hJ
  have hκ : Function.Injective κ := hv.1
  have hyk : ∀ (k : K₀) (a : ι₀ k), y ⟨κ k, bx k a⟩ = (RingHom.id Ω) (y₀ ⟨k, a⟩) := fun k a => hy ⟨k, a⟩
  have hrk : Module.finrank Ω Ω = 1 := Module.finrank_self Ω
  have hP₀ : (mCoordIdeal y₀).IsPrime := RingHom.ker_isPrime _
  obtain ⟨G₁, a₁, hG₁, hG₁P, hcount⟩ := GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.exists_count y₀ y κ bx (RingHom.id Ω) D 1
    hκ hyk hA₀ hA hB₀ hB hrk one_pos
  obtain ⟨G₃, a₃, hG₃, hG₃P, hloc3⟩ := GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.exists_local_section y₀ y κ bx
    (RingHom.id Ω) 1 hyk hP₀ hB₀ hrk one_pos
  have hTop : IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) := by
    refine ⟨{1}, ?_, Ideal.span_singleton_one.symm⟩
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨0, GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_one'⟩
  have hTopP : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y := fun h =>
    not_mem_mCoordIdeal_of_aeval_ne_zero y 1 (by simp) (h Submodule.mem_top)
  obtain ⟨J', -, hJ'h, hJ'P, ⟨R⟩⟩ := hRes K ι (mCoordIdeal y) ⊤ D hA hTop hTopP
  obtain ⟨F₁, hF₁J, hF₁P, a₄, hF₁h⟩ : ∃ F ∈ J', F ∉ mCoordIdeal y ∧ ∃ a, IsMultiHomog F a := by
    obtain ⟨S, hS, rfl⟩ := hJ'h
    by_contra hcon
    push_neg at hcon
    apply hJ'P
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    by_contra hfP
    exact hcon f (Ideal.subset_span hf) hfP a ha
  have halg1 : ∀ α : Ω, letI := (RingHom.id Ω).toAlgebra; IsAlgebraic Ω α := by
    intro α
    letI := (RingHom.id Ω).toAlgebra
    exact isAlgebraic_algebraMap (R := Ω) (A := Ω) α
  obtain ⟨G₄, a₄', hG₄h, hG₄y, hG₄z⟩ := RootFieldNumerics.Ref.Zeros.zeros_proj y₀ y (RingHom.id Ω) hv hy hB₀ halg1 hF₁h hF₁P
  have hG₄P : G₄ ∉ mCoordIdeal y₀ := not_mem_mCoordIdeal_of_aeval_ne_zero y₀ G₄ hG₄y
  have hFh := GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_mul' (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_mul' hG₁ hG₃) hG₄h
  have hFP : G₁ * G₃ * G₄ ∉ mCoordIdeal y₀ := by
    intro hm
    rcases hP₀.mem_or_mem hm with hm | hm
    · rcases hP₀.mem_or_mem hm with hm | hm
      · exact hG₁P hm
      · exact hG₃P hm
    · exact hG₄P hm
  let bk' : Unit → K₀ := fun _ => k₀
  let bx' : ∀ u : Unit, Fin (n + 1) ≃ ι₀ (bk' u) := fun _ => ix
  have hv' : IsBlockMap bk' (blkV bk' bx') :=
    GlobalTheory.CompanionTheory.Ar.Chg.isBlockMap_blkV bx' (fun a b _ => Subsingleton.elim a b)
  have hy' : ∀ p, y₀ (blkV bk' bx' p) = g ((fun p : (Σ _ : Unit, Fin (n + 1)) => yf p.2) p) :=
    fun p => hyf p.2
  have hBf := RootFieldNumerics.Ref.Zeros.birational_of_closure yf hgen
  have halg2 : ∀ α : Ω, letI := g.toAlgebra; IsAlgebraic Ωf α := by
    letI := g.toAlgebra
    haveI : FiniteDimensional Ωf Ω := Module.finite_of_finrank_pos hfin
    exact fun α => Algebra.IsAlgebraic.isAlgebraic α
  obtain ⟨G', b', hG'h, hG'y, hG'z⟩ := RootFieldNumerics.Ref.Zeros.zeros_proj
    (fun p : (Σ _ : Unit, Fin (n + 1)) => yf p.2) y₀ g hv' hy' hBf halg2 hFh hFP
  have hGh := GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_rename' hv' hG'h
  have hGy0 : aeval y₀ (rename (blkV bk' bx') G') ≠ 0 := by
    rw [MvPolynomial.aeval_rename]
    have e1 : y₀ ∘ blkV bk' bx' = fun p => g.toIntAlgHom ((fun p : (Σ _ : Unit, Fin (n + 1)) => yf p.2) p) :=
      funext hy'
    rw [e1, ← MvPolynomial.comp_aeval_apply]
    exact (map_ne_zero g).mpr hG'y
  have hGP : rename (blkV bk' bx') G' ∉ mCoordIdeal y₀ := not_mem_mCoordIdeal_of_aeval_ne_zero y₀ _ hGy0
  have hG2P : rename (blkV κ bx) (rename (blkV bk' bx') G') ∉ mCoordIdeal y := by
    apply not_mem_mCoordIdeal_of_aeval_ne_zero
    rw [MvPolynomial.aeval_rename]
    have e2 : y ∘ blkV κ bx = y₀ := funext hy
    rw [e2]
    exact hGy0
  have hnz : ∀ w ∈ mcPts (mCoordIdeal y₀),
      eval w (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) ≠ 0 →
      eval w (map (Int.castRingHom ℂ) G₁) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G₃) ≠ 0 ∧
        eval w (map (Int.castRingHom ℂ) G₄) ≠ 0 := by
    intro w hw hGw
    have hFw : eval w (map (Int.castRingHom ℂ) (G₁ * G₃ * G₄)) ≠ 0 := by
      intro h0
      apply hGw
      rw [GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.eval_map_rename']
      exact hG'z w hw h0
    simp only [map_mul, mul_ne_zero_iff] at hFw
    exact ⟨hFw.1.1, hFw.1.2, hFw.2⟩
  obtain ⟨h, hh, hho⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K₀ ι₀ K ι κ (blkV κ bx) (mCoordIdeal y₀)
    (mCoordIdeal y) J' D D R₀ R hv (GlobalTheory.CompanionTheory.Ar.Chg.mCoordIdeal_le_imageZ (RingHom.id Ω) bx hyk)
  haveI := R₀.compact
  haveI := R₀.t2
  haveI := R.compact
  haveI := R.t2
  have hdeg1 := GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg.isDegreeOff_of_correspondence K₀ ι₀ K ι (mCoordIdeal y₀) ⊤
    (mCoordIdeal y) J' D R₀.X R₀.A R₀ id R h (fun z w => SameOrbit (fun p => z (blkV κ bx p)) w)
    (rename (blkV bk' bx') G') (rename (blkV κ bx) (rename (blkV bk' bx') G')) _ _ 1 rfl hA₀ hA
    (holoMap_id _) (isDegreeOff_id _) hh hGh hGP
    (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_rename' hv hGh) hG2P
    (fun z z₁ w w₁ hr hz hw => GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_trans'
      (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_trans' (sameOrbit_comp_blkV κ bx hz) hr)
      (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' hw))
    (by
      intro x x₀ hx
      simp only [id] at hx
      subst hx
      exact GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' (hho x))
    (by
      intro x x₀ hr
      exact R₀.inj x₀ (h x) (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.not_mem_mcPts_top _)
        (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_trans' (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' hr)
          (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' (hho x))))
    (by
      intro w hw hGw
      exact hcount w hw (hnz w hw hGw).1)
    (by
      intro z hz hzJ w hw hr
      by_contra hGw
      apply (hnz w hw hGw).2.2
      have hFz : eval z (map (Int.castRingHom ℂ) F₁) = 0 := hzJ.2 F₁ hF₁J
      exact (HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG₄h hr).1 (hG₄z z hz hFz))
    (by
      intro z hz w hw hr hGw
      rw [GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.eval_map_rename']
      exact (HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hGh hr).2 hGw)
    (by
      intro z hz w₀ hw₀ hr hGw
      exact hloc3 z hz w₀ hw₀ hr (hnz w₀ hw₀ hGw).2.1)
  set S : Set X := {x | eval (fun p : (Σ _ : Unit, Fin (n + 1)) => pt x p.2) (map (Int.castRingHom ℂ) G') = 0}
    with hSdef
  have hpre : ∀ x₀ : R₀.X, (eval (R₀.lift x₀ x₀) (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) = 0
      ↔ π x₀ ∈ S) := by
    intro x₀
    obtain ⟨a, ha⟩ := hpt x₀
    have hmem : R₀.lift x₀ x₀ ∈ mcPts (mCoordIdeal y₀) := R₀.mem x₀ x₀ (R₀.mem_U x₀)
    have ha0 : a ≠ 0 := by
      rintro rfl
      obtain ⟨i, hi⟩ := hmem.1 k₀
      apply hi
      have := congrFun ha (ix.symm i)
      simpa using this
    rw [GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.eval_map_rename']
    apply HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG'h
    refine ⟨fun _ => a, fun _ => ha0, ?_⟩
    funext p
    have := congrFun ha p.2
    change R₀.lift x₀ x₀ ⟨k₀, ix p.2⟩ = a * pt (π x₀) p.2
    simpa using this
  have hNS : id '' {x : R₀.X | eval (R₀.lift x x) (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) = 0}
      ⊆ π ⁻¹' S := by
    rintro _ ⟨x₀, hx, rfl⟩
    exact (hpre x₀).1 hx
  have hint : interior (π ⁻¹' S) = ∅ := by
    have e3 : π ⁻¹' S = {x : R₀.X | eval (R₀.lift x x) (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) = 0} := by
      ext x₀
      exact (hpre x₀).symm
    rw [e3]
    exact HilbertSamuel.AnResNullForm.interior_eq_empty HilbertSamuel.NonvanishingDense.full R₀.toAnRes hA₀ hGh hGP
  have hSan : A.IsAnalyticSubset S := by
    intro x
    obtain ⟨U, lam, hU, hxU, hlam, hprop⟩ := hloc x
    have hpoly : ∀ q : MvPolynomial (Σ _ : Unit, Fin (n + 1)) ℂ,
        A.HoloOn U (fun y => eval (fun p : (Σ _ : Unit, Fin (n + 1)) => lam y p.2) q) := by
      intro q
      induction q using MvPolynomial.induction_on
      · intro j
        simp only [eval_C]
        exact analyticOnNhd_const
      · rename_i p q hp hq
        intro j
        simp only [map_add (f := _)]
        exact (hp j).add (hq j)
      · rename_i p i hp
        intro j
        simp only [map_mul, eval_X]
        exact (hp j).mul (hlam i.2 j)
    refine ⟨U, hU, hxU, 1,
      fun _ y => eval (fun p : (Σ _ : Unit, Fin (n + 1)) => lam y p.2) (map (Int.castRingHom ℂ) G'),
      fun _ => hpoly _, ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hSdef]
    constructor
    · rintro ⟨hyS, hyU⟩
      refine ⟨hyU, fun _ => ?_⟩
      obtain ⟨a₀, ha₀, he⟩ := hprop y hyU
      refine (HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG'h ⟨fun _ => a₀, fun _ => ha₀, ?_⟩).2 hyS
      funext p
      rw [he]
      rfl
    · rintro ⟨hyU, hz⟩
      refine ⟨?_, hyU⟩
      obtain ⟨a₀, ha₀, he⟩ := hprop y hyU
      refine (HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG'h ⟨fun _ => a₀, fun _ => ha₀, ?_⟩).1 (hz 0)
      funext p
      rw [he]
      rfl
  have hcomp := RootFieldNumerics.Ref.Comp.degree_comp hπ hh hd hdeg hdeg1 hSan hint hNS
  exact ⟨J', R, h, br ∪ S, hh, fun x => hho x, GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_comp hh hπ, hcomp⟩

end RootFieldNumerics.Ref
end
end
end

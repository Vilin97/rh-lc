module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSectionsLarge
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockVeronese
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionRing
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegreeSteps
public import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionRingFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeExtension

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsCoordNeZero

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section G1SpanProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartLat_mul {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n m : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a m) : s * t ∈ chartLat y a (n + m) := by
  apply _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockVeronese.chartLat_mul <;> assumption

theorem isBoundedH_mono {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {C C' : ℝ} {s : Ω}
    (h : IsBoundedH P y A τ C s) (hC : C ≤ C') : IsBoundedH P y A τ C' s := by
  intro dg dh g h' z hg hh hdeg he hz
  refine (h dg dh g h' z hg hh hdeg he hz).trans ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right hC (mul_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt (A.pos z hz.1)) _))

theorem mul_monomial_bounded (hMul : SectionBoundedMul.Statement) {y : (Σ k, ι k) → Ω} {A : HermLine ι} {q : ℕ}
    {w : Fin q → Ω} (hw : ∀ j, w j ∈ chartLat y A.a 1)
    (hsmall : ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) {x : Ω} {n : ℕ} {C : ℝ}
    (hx : x ∈ chartLat y A.a n) (hb : IsBoundedH (mCoordIdeal y) y A n C x) (μ : Fin q → ℕ) :
    x * ∏ j, w j ^ μ j ∈ chartLat y A.a (n + ∑ j, μ j) ∧
      IsBoundedH (mCoordIdeal y) y A (n + ∑ j, μ j) C (x * ∏ j, w j ^ μ j) := by
  have step : ∀ {x' : Ω} {n' : ℕ} (j : Fin q), x' ∈ chartLat y A.a n' →
      IsBoundedH (mCoordIdeal y) y A n' C x' →
      x' * w j ∈ chartLat y A.a (n' + 1) ∧ IsBoundedH (mCoordIdeal y) y A (n' + 1) C (x' * w j) := by
    intro x' n' j hx' hb'
    refine ⟨chartLat_mul hx' (hw j), ?_⟩
    have := hMul K ι Ω y A n' 1 C 1 x' (w j) hx' (hw j) hb' (isBoundedH_one_of_isSmallH (hsmall j))
    rwa [mul_one] at this
  have hpow : ∀ (j : Fin q) (k : ℕ) {x' : Ω} {n' : ℕ}, x' ∈ chartLat y A.a n' →
      IsBoundedH (mCoordIdeal y) y A n' C x' →
      x' * w j ^ k ∈ chartLat y A.a (n' + k) ∧ IsBoundedH (mCoordIdeal y) y A (n' + k) C (x' * w j ^ k) := by
    intro j k
    induction k with
    | zero => intro x' n' hx' hb'; simpa using ⟨hx', hb'⟩
    | succ k ih =>
      intro x' n' hx' hb'
      obtain ⟨h1, h2⟩ := ih hx' hb'
      have := step j h1 h2
      rw [pow_succ, ← mul_assoc, ← add_assoc]
      exact this
  have hS : ∀ S : Finset (Fin q), x * ∏ j ∈ S, w j ^ μ j ∈ chartLat y A.a (n + ∑ j ∈ S, μ j) ∧
      IsBoundedH (mCoordIdeal y) y A (n + ∑ j ∈ S, μ j) C (x * ∏ j ∈ S, w j ^ μ j) := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => simpa using ⟨hx, hb⟩
    | insert a S ha ih =>
      obtain ⟨h1, h2⟩ := hpow a (μ a) ih.1 ih.2
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have e1 : x * (w a ^ μ a * ∏ j ∈ S, w j ^ μ j) = (x * ∏ j ∈ S, w j ^ μ j) * w a ^ μ a := by ring
      have e2 : n + (μ a + ∑ j ∈ S, μ j) = n + ∑ j ∈ S, μ j + μ a := by ring
      rw [e1, e2]
      exact ⟨h1, h2⟩
  exact hS Finset.univ

theorem exists_coord_ne_zero {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := hV.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

end G1SpanProof

theorem SuccessiveMinimaSpan.proof (hFin : SectionRingFinite.Statement) (hBd : SectionBounded.Statement)
    (hMul : SectionBoundedMul.Statement) : SuccessiveMinimaSpan.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 _ hV _ hA
  obtain ⟨q, w, hw, hgen, hsmall⟩ := hA.gen
  obtain ⟨r, d, e, he, hspan⟩ :=
    hFin K ι Ω y A.a q w (exists_coord_ne_zero hV) hw hgen
  have hCe : ∀ i, ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A (d i) C (e i) := fun i =>
    hBd K ι Ω y A q w hw hgen hsmall (d i) (e i) (he i)
  choose Ce hCe using hCe
  refine ⟨∑ i, |Ce i|, fun n => le_antisymm ?_ ?_⟩
  · rw [AddSubgroup.closure_le]
    exact fun s hs => hs.1
  · refine (hspan n).trans (AddSubgroup.closure_mono ?_)
    rintro s ⟨i, μ, hn, rfl⟩
    obtain ⟨h1, h2⟩ := mul_monomial_bounded hMul hw hsmall (he i) (hCe i) μ
    rw [hn] at h1 h2
    refine ⟨h1, isBoundedH_mono h2 ?_⟩
    exact (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Ce i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module

theorem CovolumeLeGram.proof : CovolumeLeGram.Statement := by
  intro n L _ _ ι _ _ x hxL hx hcard
  have hcard' : Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hcard, finrank_euclideanSpace_fin]
  let B : Basis ι ℝ (EuclideanSpace ℝ (Fin n)) := basisOfLinearIndependentOfCardEqFinrank' x hx hcard'
  have hB : ⇑B = x := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hML : Submodule.span ℤ (Set.range B) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; rw [hB]; exact hxL i)
  have hcovM : ZLattice.covolume (Submodule.span ℤ (Set.range B)) = Real.sqrt (Matrix.gram ℝ x).det := by
    rw [GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram _ (B.restrictScalars ℤ)]
    congr 3
    funext i
    simp [Basis.restrictScalars_apply, hB]
  have hdiv := ZLattice.covolume_div_covolume_eq_relIndex' _ L hML
  have hposM := ZLattice.covolume_pos (Submodule.span ℤ (Set.range B))
  have hposL := ZLattice.covolume_pos L
  have hne : (Submodule.span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hdiv
    exact (div_pos hposM hposL).ne' hdiv
  have h1 : (1 : ℝ) ≤ ZLattice.covolume (Submodule.span ℤ (Set.range B)) / ZLattice.covolume L := by
    rw [hdiv]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  rw [← hcovM]
  rwa [le_div_iff₀ hposL, one_mul] at h1

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanningExtension

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module Set

theorem SpanningExtension.proof : SpanningExtension.Statement := by
  intro V _ _ _ ι _ v S hv hS
  classical
  set s : Set V := range v with hs_def
  have hs : LinearIndepOn ℝ id s := (linearIndepOn_id_range_iff hv.injective).mpr hv
  have hst : s ⊆ s ∪ S := subset_union_left
  set b := hs.extend hst with hb_def
  have hsb : s ⊆ b := hs.subset_extend hst
  have hbt : b ⊆ s ∪ S := hs.extend_subset hst
  have hbli : LinearIndependent ℝ (fun x : b => (x : V)) := hs.linearIndepOn_extend hst
  have hspan : ⊤ ≤ Submodule.span ℝ (range (fun x : b => (x : V))) := by
    rw [Subtype.range_coe, ← hS]
    exact Submodule.span_le.2 (subset_union_right.trans (hs.subset_span_extend hst))
  let B := Basis.mk hbli hspan
  have hcard_b : Nat.card b = finrank ℝ V := (finrank_eq_nat_card_basis B).symm
  have : Finite b := Module.Finite.finite_basis B
  have hbfin : b.Finite := toFinite b
  have hcard_s : s.ncard = Fintype.card ι := by
    rw [hs_def, ncard_range_of_injective hv.injective, Nat.card_eq_fintype_card]
  have hk : Nat.card (b \ s : Set V) = finrank ℝ V - Fintype.card ι := by
    rw [Nat.card_coe_set_eq, ncard_sdiff hsb (hbfin.subset hsb), ← hcard_s, ← Nat.card_coe_set_eq,
      hcard_b]
  let e : (b \ s : Set V) ≃ Fin (finrank ℝ V - Fintype.card ι) := Finite.equivFinOfCardEq hk
  let w : Fin (finrank ℝ V - Fintype.card ι) → V := fun j => (e.symm j : V)
  have hw_mem : ∀ j, w j ∈ b \ s := fun j => (e.symm j).2
  refine ⟨w, fun j => ?_, ?_⟩
  · obtain ⟨hb, hns⟩ := hw_mem j
    rcases hbt hb with h | h
    · exact absurd h hns
    · exact h
  · let f : ι ⊕ Fin (finrank ℝ V - Fintype.card ι) → b :=
      Sum.elim (fun i => ⟨v i, hsb (mem_range_self i)⟩) (fun j => ⟨w j, (hw_mem j).1⟩)
    have hf : Function.Injective f := by
      rintro (i | j) (i' | j') h <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      · rw [hv.injective h]
      · exact absurd (h ▸ mem_range_self i) (hw_mem j').2
      · exact absurd (h ▸ mem_range_self i') (hw_mem j).2
      · rw [e.symm.injective (Subtype.ext h)]
    have : Sum.elim v w = (fun x : b => (x : V)) ∘ f := by
      funext x; rcases x with i | j <;> rfl
    rw [this]
    exact hbli.comp f hf

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeDegree

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module

theorem SublatticeDegree.proof (hExt : SublatticeExtension.Statement) (hSpan : SpanningExtension.Statement)
    (hCov : CovolumeLeGram.Statement) (hGram : GramContraction.Statement) : SublatticeDegree.Statement := by
  intro E E' _ _ R R' φ φ' _ _ _ _ ψ S C hφ hφ' hψ hnorm hS hSC hC
  obtain ⟨Ψ, hΨφ, hΨn, hΨi⟩ := hExt E E' R R' φ φ' ψ hφ hφ' hψ hnorm
  set Λ := imageLattice φ with hΛdef
  set Λ' := imageLattice φ' with hΛ'def
  have hC0 : 0 < C := by linarith

  have hrk : finrank ℤ Λ' = R' := by rw [ZLattice.rank ℝ Λ', finrank_euclideanSpace_fin]
  let b' : Basis (Fin R') ℤ Λ' := Module.finBasisOfFinrankEq ℤ Λ' hrk
  let u : Fin R' → EuclideanSpace ℝ (Fin R') := fun i => (b' i : EuclideanSpace ℝ (Fin R'))
  have hcov' : ZLattice.covolume Λ' = Real.sqrt (Matrix.gram ℝ u).det :=
    GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram Λ' b'
  have hu : LinearIndependent ℝ u := by
    have he : ⇑(b'.ofZLatticeBasis ℝ Λ') = u := funext fun i => b'.ofZLatticeBasis_apply ℝ Λ' i
    rw [← he]
    exact Basis.linearIndependent _
  have hv : LinearIndependent ℝ (Ψ ∘ u) := hu.map' Ψ (LinearMap.ker_eq_bot.2 hΨi)
  have hRR : R' ≤ R := by simpa using hv.fintype_card_le_finrank

  have hspan : Submodule.span ℝ (φ '' S) = ⊤ := by
    have h1 : (Λ : Set (EuclideanSpace ℝ (Fin R))) ⊆ Submodule.span ℝ (φ '' S) := by
      intro x hx
      obtain ⟨e, rfl⟩ := AddMonoidHom.mem_range.1 hx
      clear hx
      have he : e ∈ AddSubgroup.closure S := hS ▸ AddSubgroup.mem_top e
      induction he using AddSubgroup.closure_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | neg x _ hx => simpa using neg_mem hx
    rw [eq_top_iff, ← (IsZLattice.span_top : Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin R))) = ⊤)]
    exact Submodule.span_le.2 h1

  obtain ⟨w, hwS, hind⟩ := hSpan (EuclideanSpace ℝ (Fin R)) (Fin R') (Ψ ∘ u) (φ '' S) hv hspan
  have hcard : Fintype.card (Fin R' ⊕ Fin (finrank ℝ (EuclideanSpace ℝ (Fin R)) - Fintype.card (Fin R'))) = R := by
    simp only [Fintype.card_sum, Fintype.card_fin, finrank_euclideanSpace_fin]
    omega
  have hmem : ∀ i, Sum.elim (Ψ ∘ u) w i ∈ Λ := by
    rintro (i | j)
    · obtain ⟨e, he⟩ := AddMonoidHom.mem_range.1 (b' i).2
      refine AddMonoidHom.mem_range.2 ⟨ψ e, ?_⟩
      simp only [Sum.elim_inl, Function.comp_apply, u, ← he, hΨφ]
    · obtain ⟨s, _, hsw⟩ := hwS j
      simp only [Sum.elim_inr]
      rw [← hsw]
      exact AddMonoidHom.mem_range.2 ⟨s, rfl⟩
  have h1 := hCov R Λ _ (Sum.elim (Ψ ∘ u) w) hmem hind hcard
  have h2 := hGram (Fin R') _ (EuclideanSpace ℝ (Fin R)) Ψ u w hΨn

  have hw : ∀ j, ‖w j‖ ≤ C := fun j => by
    obtain ⟨s, hs, hsw⟩ := hwS j
    rw [← hsw]
    exact hSC s hs
  have hk : Fintype.card (Fin (finrank ℝ (EuclideanSpace ℝ (Fin R)) - Fintype.card (Fin R'))) ≤ R := by
    simp only [Fintype.card_fin, finrank_euclideanSpace_fin]
    omega
  have hprod : ∏ j, ‖w j‖ ^ 2 ≤ (C ^ R) ^ 2 := by
    calc ∏ j, ‖w j‖ ^ 2 ≤ ∏ _j, C ^ 2 :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hw j) 2)
      _ = (C ^ 2) ^ Fintype.card (Fin (finrank ℝ (EuclideanSpace ℝ (Fin R)) - Fintype.card (Fin R'))) := by
          rw [Finset.prod_const, Finset.card_univ]
      _ ≤ (C ^ 2) ^ R := pow_le_pow_right₀ (by nlinarith) hk
      _ = (C ^ R) ^ 2 := by ring
  have hpos' : 0 < ZLattice.covolume Λ' := ZLattice.covolume_pos Λ'
  have hpos : 0 < ZLattice.covolume Λ := ZLattice.covolume_pos Λ
  have hdu : 0 ≤ (Matrix.gram ℝ u).det := by
    rw [hcov'] at hpos'
    exact (Real.sqrt_pos.1 hpos').le
  have hmain : ZLattice.covolume Λ ≤ ZLattice.covolume Λ' * C ^ R := by
    calc ZLattice.covolume Λ ≤ Real.sqrt (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det := h1
      _ ≤ Real.sqrt ((Matrix.gram ℝ u).det * (C ^ R) ^ 2) :=
          Real.sqrt_le_sqrt (h2.trans (mul_le_mul_of_nonneg_left hprod hdu))
      _ = ZLattice.covolume Λ' * C ^ R := by
          rw [Real.sqrt_mul hdu, Real.sqrt_sq (pow_pos hC0 R).le, hcov']
  have hlog := Real.log_le_log hpos hmain
  rw [Real.log_mul hpos'.ne' (pow_pos hC0 R).ne', Real.log_pow] at hlog
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SublatticeDegree.full : SublatticeDegree.Statement :=
  SublatticeDegree.proof SublatticeExtension.proof SpanningExtension.proof CovolumeLeGram.proof
    GramContraction.proof

theorem SuccessiveMinimaSpan.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement) : SuccessiveMinimaSpan.Statement :=
  SuccessiveMinimaSpan.proof
    (SectionRingFinite.proof (SectionLatticeFinite.proof hC)
      (SectionSpanStep.proof (SpanStepHomog.proof (SpanStepLocal.proof (RelLatticeFinite.proof hR)))
        SerreGraded.proof))
    SectionBounded.proof SectionBoundedMul.proof

end GroundTheory.Heights₂.Heights.Targets
end
end

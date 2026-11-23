module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.OpenSubgroup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseDisjointParahoricTorusDoubleCosetAntitonStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexTwoBlockParahoricConjTorusDiagElementStatement
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroupStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.isOpen_isCompact_twoBlockParahoricSubgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) ∧ IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  first | exact @GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric | exact GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric | (intros; apply GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMul

section

@[expose] public section

open MeasureTheory Pointwise

namespace GlobalTheory

theorem mem_map_conj_iff_conj_mem {G : Type} [Group G] (J : Subgroup G) (g x : G) :
    x ∈ J.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem measureReal_doubleCoset_eq_relIndex_mul :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  intro G _ _ _ _ _ μ _ J hJo hJc g
  set K := J.map (MulAut.conj g).toMonoidHom with hK
  set H : Subgroup J := K.subgroupOf J with hH
  haveI : CompactSpace J := isCompact_iff_compactSpace.1 hJc
  have hKo : IsOpen (K : Set G) := by
    have : (K : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
      ext x; rw [SetLike.mem_coe, hK, mem_map_conj_iff_conj_mem]; rfl
    rw [this]; exact hJo.preimage (by fun_prop)
  have hHo : IsOpen (H : Set J) := by
    have : (H : Set J) = Subtype.val ⁻¹' (K : Set G) := by
      ext x; simp [hH, Subgroup.mem_subgroupOf]
    rw [this]; exact hKo.preimage continuous_subtype_val
  haveI : Finite (J ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (J ⧸ H) := Fintype.ofFinite _
  let f : J ⧸ H → Set G := fun q => ((q.out : J) * g : G) • (J : Set G)
  have hcover : DoubleCoset.doubleCoset g (J : Set G) (J : Set G) = ⋃ q, f q := by
    ext x
    simp only [DoubleCoset.doubleCoset, Set.mem_mul, Set.mem_singleton_iff, Set.mem_iUnion, f,
      Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ⟨j, hj, b, hb, rfl⟩, k, hk, rfl⟩
      rw [hb]
      refine ⟨(QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H), ?_⟩
      set o := (Quotient.out (QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H) : J) with ho
      have h1 : (QuotientGroup.mk o : J ⧸ H) = QuotientGroup.mk (⟨j, hj⟩ : J) := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq] at h1
      have h2 : ((o : G))⁻¹ * j ∈ K := by
        have := Subgroup.mem_subgroupOf.1 (hH ▸ h1)
        simpa using this
      rw [hK, mem_map_conj_iff_conj_mem] at h2
      refine ⟨g⁻¹ * ((o : G)⁻¹ * j) * g * k, J.mul_mem h2 hk, ?_⟩
      group
    · rintro ⟨q, y, hy, rfl⟩
      exact ⟨(q.out : J) * g, ⟨(q.out : J), (q.out : J).2, g, rfl, rfl⟩, y, hy, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 ?_
    rintro x hx hx'
    simp only [f, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', hxy⟩ := hx'
    apply hqq'
    have e : ((q.out : J) : G) = (q'.out : J) * g * y' * y⁻¹ * g⁻¹ := by
      rw [hxy]; group
    have hmem : (q.out)⁻¹ * q'.out ∈ H := by
      change _ ∈ K.subgroupOf J
      rw [Subgroup.mem_subgroupOf, hK, mem_map_conj_iff_conj_mem]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      have : g⁻¹ * ((((q'.out : J) : G) * g * y' * y⁻¹ * g⁻¹)⁻¹ * (q'.out : J)) * g = y * y'⁻¹ := by group
      rw [this]
      exact J.mul_mem hy (J.inv_mem hy')
    have := (QuotientGroup.eq (s := H)).2 hmem
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  have hmeas : ∀ q, MeasurableSet (f q) := fun q =>
    (hJo.smul ((q.out : J) * g : G)).measurableSet
  have hval : ∀ q, μ (f q) = μ (J : Set G) := fun q => measure_smul μ _ _
  have hfin : μ (J : Set G) ≠ ⊤ := (hJc.measure_lt_top).ne
  rw [hcover, measureReal_def, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def, Subgroup.relIndex,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMulStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  first | exact @GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | exact GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | (intros; apply GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjUniformizerPowerDiagonalGLReindex

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.ReindexTorus

def reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') : GL n k ≃* GL n' k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k σ).toMulEquiv

theorem val_reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') (g : GL n k) : (reindexGL k σ g).val = Matrix.reindex σ σ g.val := rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem map_reindexGL_KO (σ : n ≃ n') : (KO k n).map (reindexGL k σ).toMonoidHom = KO k n' := by
  ext x
  rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff]
  have h1 : ∀ i j, ((reindexGL k σ).symm x).val i j = x.val (σ i) (σ j) := fun i j => rfl
  have h2 : ∀ i j, (((reindexGL k σ).symm x)⁻¹).val i j = (x⁻¹).val (σ i) (σ j) := fun i j => by
    rw [← map_inv]; rfl
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, h1, h2]
  exact and_congr ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩
    ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩

theorem reindexGL_torusElt (σ : n ≃ n') (ϖ : kˣ) (e : n → ℤ) :
    reindexGL k σ (torusElt k n ϖ e) = torusElt k n' ϖ (e ∘ σ.symm) := by
  refine Units.ext ?_
  rw [val_reindexGL, val_torusElt, val_torusElt, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  rfl

theorem relIndex_conj_torusElt_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n ≃ n') (e : n → ℤ),
    ((KO k n').map (MulAut.conj (torusElt k n' ϖ (e ∘ σ.symm))).toMonoidHom).relIndex (KO k n') =
      ((KO k n).map (MulAut.conj (torusElt k n ϖ e)).toMonoidHom).relIndex (KO k n) := by
  intro k _ _ _ _ ϖ n n' _ _ _ _ σ e
  set φ := reindexGL k σ
  have hconj : ∀ g : GL n k, ∀ H : Subgroup (GL n k),
      (H.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
        (H.map φ.toMonoidHom).map (MulAut.conj (φ g)).toMonoidHom := by
    intro g H
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x : 1
    simp [φ, map_mul, map_inv]
  have hK := map_reindexGL_KO k σ
  rw [← reindexGL_torusElt k σ ϖ e, ← hK, ← hconj]
  have key : ∀ A B : Subgroup (GL n k), (A.map φ.toMonoidHom).relIndex (B.map φ.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.map_equiv_eq_comap_symm' φ A, Subgroup.relIndex_comap, Subgroup.map_map]
    have : (φ.symm.toMonoidHom.comp φ.toMonoidHom) = MonoidHom.id _ := by ext x : 1; simp
    rw [this, Subgroup.map_id]
  exact key _ _

end GlobalTheory.ReindexTorus
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedPlaceDoubleCosetVolumeAndDisjoint

section

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainCells

theorem vol_dcell_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] [BorelSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k))
    [μK.IsHaarMeasure], μK (KO k (Fin (l * t))) = 1 →
  (∀ e : Fin (l * t) → ℤ, m.real (dcell ϖ (e ∘ (blkEquiv l t).symm)) =
    (resCard k : ℝ) ^ ((r : ℤ) * sumAbs e) * μK.real (cell k (Fin (l * t)) ϖ e)) ∧
  Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t _ _ m _ hm _ _ μK _ hμK
  refine ⟨fun e => ?_, GlobalTheory.T.pairwise_disjoint_parahoricTorusDoubleCoset_antitone k ϖ hϖ r l t⟩
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_twoBlockParahoricSubgroup k (Fin r) (Blocks l t)
  have h1 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul m _ ho hc (mtor (A := Fin r) ϖ (e ∘ (blkEquiv l t).symm))
  have h2 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul μK (KO k (Fin (l * t))) SplitFlip.isOpen_KO SplitFlip.isCompact_KO (torusElt k _ ϖ e)
  have hs : sumAbs (e ∘ (blkEquiv l t).symm) = sumAbs e := by
    unfold sumAbs; exact Equiv.sum_comp (blkEquiv l t).symm (fun i => |e i|)
  have hm1 : m.real (parahoric k (Fin r) (Blocks l t) : Set _) = 1 := by simp [Measure.real, hm]
  have hK1 : μK.real (KO k (Fin (l * t)) : Set _) = 1 := by simp [Measure.real, hμK]
  rw [dcell, h1, cell, h2, hm1, hK1, GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement k ϖ hϖ, GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex k ϖ _ _ (blkEquiv l t), hs]
  simp

end GlobalTheory.ChainCells
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedPlaceDoubleCosetVolumeAndDisjointStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.twistedPlace_doubleCoset_volume_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] [BorelSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k))
    [μK.IsHaarMeasure], μK (KO k (Fin (l * t))) = 1 →
  (∀ e : Fin (l * t) → ℤ, m.real (dcell ϖ (e ∘ (blkEquiv l t).symm)) =
    (resCard k : ℝ) ^ ((r : ℤ) * sumAbs e) * μK.real (cell k (Fin (l * t)) ϖ e)) ∧
  Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  first | exact @GlobalTheory.ChainCells.vol_dcell_and_disjoint | exact GlobalTheory.ChainCells.vol_dcell_and_disjoint | (intros; apply GlobalTheory.ChainCells.vol_dcell_and_disjoint <;> assumption)
end
end

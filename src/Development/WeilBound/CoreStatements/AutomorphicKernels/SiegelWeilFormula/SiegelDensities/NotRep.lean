module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGram
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZeroStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddBlockAnisotropic
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.SWMeasCAll
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.TprodMemNnRealSet

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open NumberField IsDedekindDomain Topology Filter

def nnRealSet : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}

theorem isClosed_nnRealSet : IsClosed nnRealSet :=
  (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)

theorem mul_mem_nnRealSet {a b : ℂ} (ha : a ∈ nnRealSet) (hb : b ∈ nnRealSet) : a * b ∈ nnRealSet := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, ?_⟩
  · simp [Complex.mul_im, ha1, hb1]
  · simp only [Complex.mul_re, ha1, hb1, mul_zero, sub_zero]
    exact mul_nonneg ha2 hb2

theorem one_mem_nnRealSet : (1 : ℂ) ∈ nnRealSet := ⟨by simp, by simp⟩

theorem prod_mem_nnRealSet {ι : Type} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i, f i ∈ nnRealSet) :
    ∏ i ∈ s, f i ∈ nnRealSet := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_nnRealSet
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact mul_mem_nnRealSet (hf a) ih

theorem tprod_mem_nnRealSet {ι : Type} (f : ι → ℂ) (hf : ∀ i, f i ∈ nnRealSet) : ∏' i, f i ∈ nnRealSet := by
  by_cases h : Multipliable f
  · exact isClosed_nnRealSet.mem_of_tendsto h.hasProd (Eventually.of_forall fun s => prod_mem_nnRealSet s f hf)
  · rw [tprod_eq_one_of_not_multipliable h]
    exact one_mem_nnRealSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem factor_mem (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) (hs : 0 ≤ s) :
    (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∈ nnRealSet := by
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 h
  have hq0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hp : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) = (((Ideal.absNorm v.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hq0]
    push_cast
    rfl
  have hle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)
  have hpos : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) := Real.rpow_nonneg hq0 _
  rw [hp]
  unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs
  · refine ⟨by simp, ?_⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.one_im, Complex.ofReal_im]
    nlinarith
  · refine ⟨by simp, ?_⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.one_im,
      Complex.ofReal_im]
    nlinarith

theorem lamLim_real {Λ : ℂ} (h : IsLamLim F E Λ) : Λ = ((Λ.re : ℝ) : ℂ) ∧ 0 ≤ Λ.re := by
  have hmem : Λ ∈ nnRealSet := by
    refine isClosed_nnRealSet.mem_of_tendsto h ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact tprod_mem_nnRealSet _ fun v => factor_mem v s (by linarith [Set.mem_Ioi.1 hs])
  refine ⟨?_, hmem.2⟩
  apply Complex.ext <;> simp [hmem.1]

theorem lamLim_unique {Λ Λ' : ℂ} (h : IsLamLim F E Λ) (h' : IsLamLim F E Λ') : Λ = Λ' :=
  tendsto_nhds_unique h h'

end PositivityTheory.SiegelWeilFormula.Densx

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.NotRep

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

def halfLam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : ℝ≥0 := by
  classical
  exact if h : ∃ Λ : ℂ, IsLamLim F E Λ then Real.toNNReal (h.choose.re / 2) else 0

theorem halfLam_spec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Λ : ℂ)
    (hΛ : IsLamLim F E Λ) : ((halfLam F E : ℝ) : ℂ) = Λ / 2 := by
  classical
  have h : ∃ Λ : ℂ, IsLamLim F E Λ := ⟨Λ, hΛ⟩
  have he : h.choose = Λ := lamLim_unique h.choose_spec hΛ
  obtain ⟨h1, h2⟩ := lamLim_real hΛ
  rw [halfLam, dite_eq_left h, he, Real.coe_toNNReal _ (by linarith)]
  conv_rhs => rw [h1]
  push_cast
  ring

theorem notRepC_of (hE1 : PositivityTheory.PfSWUS.HMass.OneVecBinary) (hM : MassCAll) : NotRepC := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM1 hA t ht T hT hdet hT' hne
  intro d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf m hminf hm
  refine ⟨halfLam F E, ?_, fun Λ hΛ => halfLam_spec Λ hΛ⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hLinf : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v : HeightOneSpectrum (𝓞 F), IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  have haarOf : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
      [BorelSpace R], IsLocR R → ∀ lam' : Measure R, lam'.IsAddHaarMeasure →
      (∀ n' M' : ℕ, (coordW R b lam' n' M').IsAddHaarMeasure) ∧
        ∀ n' : ℕ, (coordHerm R σ b lam' n').IsAddHaarMeasure := by
    intro R _ _ _ _ _ hLoc lam' hl
    obtain ⟨_, _, _, _, -⟩ := hLoc
    exact (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam' hl).2
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun _ _ => σ.commutes t
  have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
  have hdet1 : T1.det ≠ 0 := by
    rw [Matrix.det_fin_one]; exact htE
  have hsw := PositivityTheory.PfSWUS.HMass.one_vec_sw hE1 F E σ hCM (M + 1) J hJ (by omega) (Or.inr hA) T1 hT1 hdet1
  obtain ⟨minf1, hminf1⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM (M + 1) J hJ (Ainf F) hLinf 1 _ _
    ((haarOf _ hLinf laminf hinf.1).1 1 (M + 1)) ((haarOf _ hLinf laminf hinf.1).2 1)
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m' : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E),
      IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 (M + 1)) (coordHerm (Fv F v) σ b (lam v) 1) m' :=
    fun v => GlobalTheory.T.exists_gram_fiber_measures F E σ hCM (M + 1) J hJ (Fv F v) (hLv v) 1 _ _
      ((haarOf _ (hLv v) (lam v) (hv v).1).1 1 (M + 1)) ((haarOf _ (hLv v) (lam v) (hv v).1).2 1)
  choose m1 hm1 using hex
  have hEul := hsw d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf1 m1 hminf1 hm1
  have hS1 : {X : Fin 1 → Fin (M + 1) → E | gramE σ J X = T1} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    exact hne (X 0) (congrFun (congrFun hX 0) 0)
  have hS : {X : Fin (M + 1) → Fin (M + 1) → E | gramE σ J X = blockOne (algebraMap F E t) T} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    apply hne (X 0)
    simpa [gramE, blockOne] using congrFun (congrFun hX 0) 0
  have hz := ((GlobalTheory.T.euler_product_measure_zero F E σ hCM d b 1 (M + 1) _ 1 _ _).1 hEul
    (SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS1))
  have hvan : minf (hermOf (Ainf F) σ (blockOne (algebraMap F E t) T) hT') = 0 ∨
      ∃ v, cfac E v • m v (hermOf (Fv F v) σ (blockOne (algebraMap F E t) T) hT') = 0 := by
    rcases hz with h | h | ⟨v, h⟩
    · exact absurd h one_ne_zero
    · exact Or.inl (SwEmpty.fibre_zero_of_one σ hCM J hJ (Ainf F) hLinf b laminf hinf.1 t ht T hT' T1 rfl hT1
        minf1 minf hminf1 hminf h)
    · refine Or.inr ⟨v, ?_⟩
      rw [SwEmpty.fibre_zero_of_one σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hv v).1 t ht T hT' T1 rfl hT1
        (m1 v) (m v) (hm1 v) (hm v) h, smul_zero]
  have hdetB : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [((GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M T t).1)]
    exact mul_ne_zero htE hdet
  obtain ⟨hfin, hsum⟩ := hM F E σ hCM (M + 1) (by omega) J hJ (blockOne (algebraMap F E t) T) hT' hdetB d b lam
    (fun v => hv v) m hm
  rw [SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS]
  exact (GlobalTheory.T.euler_product_measure_zero F E σ hCM d b (M + 1) (M + 1) 0 (halfLam F E) _ _).2.2 hfin hsum hvan

end PositivityTheory.SiegelWeilFormula.Densx

end
end
end

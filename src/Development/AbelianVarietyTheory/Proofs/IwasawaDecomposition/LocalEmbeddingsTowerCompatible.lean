module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPowStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentCompletionOfIrreducibleMinpolyAStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsDifferByDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyIrreducibleLocalEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExtStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTop
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuousStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.adicCompletion_trace_norm_continuous_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) := by
  first | exact @GlobalTheory.adicCompletion_trace_norm_continuous | exact GlobalTheory.adicCompletion_trace_norm_continuous | (intros; apply GlobalTheory.adicCompletion_trace_norm_continuous <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormOfBasisImage

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.adicCompletion_trace_norm_of_basis_image : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L) (b' : Module.Basis (Fin n) (v.adicCompletion K) (v'.adicCompletion L)), (∀ i, b' i = algebraMap L _ (b i)) → ∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) ∧ Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z) := by
  intro K L _ _ _ _ _ v v' f hf
  letI := f.toAlgebra
  intro n b b' hb z
  have hM : Algebra.leftMulMatrix b' (algebraMap L (v'.adicCompletion L) z) =
      (Algebra.leftMulMatrix b z).map (algebraMap K (v.adicCompletion K)) := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have key : algebraMap L (v'.adicCompletion L) z * b' j =
        ∑ k, (algebraMap K (v.adicCompletion K) (b.repr (z * b j) k)) • b' k := by
      rw [hb, ← map_mul]
      conv_lhs => rw [← b.sum_repr (z * b j)]

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
    rw [key, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.norm_eq_matrix_det b', hM,
    Algebra.trace_eq_matrix_trace b, Algebra.norm_eq_matrix_det b]
  refine ⟨?_, ?_⟩
  · exact (AddMonoidHom.map_trace (algebraMap K (v.adicCompletion K)).toAddMonoidHom _).symm
  · exact (RingHom.map_det _ _).symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormOfBasisImageStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.adicCompletion_trace_norm_of_basis_image_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L) (b' : Module.Basis (Fin n) (v.adicCompletion K) (v'.adicCompletion L)), (∀ i, b' i = algebraMap L _ (b i)) → ∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) ∧ Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z) := by
  first | exact @GlobalTheory.adicCompletion_trace_norm_of_basis_image | exact GlobalTheory.adicCompletion_trace_norm_of_basis_image | (intros; apply GlobalTheory.adicCompletion_trace_norm_of_basis_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIsoStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.decomposition_group_local_galois_iso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∃ θ : Dec (F := E) A ≃* GalLoc w, Continuous θ ∧ Continuous θ.symm ∧ ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω) := by
  first | exact @GlobalTheory.LocDec.decomposition_mulEquiv_galLoc | exact GlobalTheory.LocDec.decomposition_mulEquiv_galLoc | (intros; apply GlobalTheory.LocDec.decomposition_mulEquiv_galLoc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTopStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.span_basis_image_adicCompletion_eq_top_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), Submodule.span (v.adicCompletion K) (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) = ⊤ := by
  first | exact @GlobalTheory.span_basis_image_adicCompletion_eq_top | exact GlobalTheory.span_basis_image_adicCompletion_eq_top | (intros; apply GlobalTheory.span_basis_image_adicCompletion_eq_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowOfIsPlaceOver

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LyingOver

theorem valuation_pow_of_isPlaceOver : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v → IsPlaceOver A v' → ∃ e : ℕ, 0 < e ∧ ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e := by
  intro K L Ω _ _ _ _ _ _ _ _ _ A v v' hv hv'
  have hcomap : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, ← hv x, ← hv' (algebraMap (𝓞 K) (𝓞 L) x)]
    have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
    rw [this, ← IsScalarTower.algebraMap_apply]
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨hcomap.symm⟩
  refine ⟨v.asIdeal.ramificationIdx' v'.asIdeal,
    Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v'.asIdeal v.ne_bot), ?_⟩
  intro x
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal v'.asIdeal v.ne_bot]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v v' x).symm

end GlobalTheory.LyingOver
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowOfIsPlaceOverStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.valuation_pow_of_isPlaceOver_alt : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v → IsPlaceOver A v' → ∃ e : ℕ, 0 < e ∧ ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e := by
  first | exact @GlobalTheory.LyingOver.valuation_pow_of_isPlaceOver | exact GlobalTheory.LyingOver.valuation_pow_of_isPlaceOver | (intros; apply GlobalTheory.LyingOver.valuation_pow_of_isPlaceOver <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatible

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

theorem GlobalTheory.LocalExtCompletion.exists_completion_ext : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (_ : IsPlaceOver A v'), IsLocalExt L h → ∀ (ι : Ω →ₐ[K] Kbar v) (ι' : Ω →ₐ[L] Kbar v'), IsLocEmb A v ι → IsLocEmb A v' ι' → ∃ (f : v.adicCompletion K →+* v'.adicCompletion L) (b : Kbar v ≃+* Kbar v'), Continuous f ∧ (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) ∧ (∀ z, b (ι z) = ι' z) ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ (letI := f.toAlgebra; Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L ∧ Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ (∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) ∧ ∀ z : L, Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' hloc ι ι' hι hι'
  obtain ⟨e, he, hv⟩ := GlobalTheory.T.valuation_pow_of_isPlaceOver_alt K L Ω A v v' h h'
  obtain ⟨f, hfc, hfK, hfv⟩ := GlobalTheory.T.exists_extension_pow_alt K L v v' e he hv
  have hirr := GlobalTheory.T.minpoly_irreducible_local_embedding K L Ω A v h (fun σ => by
    obtain ⟨τ, hτ⟩ := hloc σ
    exact ⟨τ, Weil_le_Dec h τ.2, hτ⟩) ι hι
  letI : Algebra (v.adicCompletion K) (v'.adicCompletion L) := f.toAlgebra
  have hind := GlobalTheory.T.linearIndependent_completion_of_irreducible_minpoly_alt K L v v' f hfK hirr _ (Module.finBasis K L)
  have hspan := GlobalTheory.T.span_basis_image_adicCompletion_eq_top_alt K L v v' f hfc hfK _ (Module.finBasis K L)
  let b' : Module.Basis (Fin (Module.finrank K L)) (v.adicCompletion K) (v'.adicCompletion L) :=
    Module.Basis.mk hind hspan.ge
  have hb' : ∀ i, b' i = algebraMap L _ (Module.finBasis K L i) := fun i => Module.Basis.mk_apply _ _ _
  haveI hfd : FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) := Module.Finite.of_basis b'
  have hrank : Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L := by
    rw [Module.finrank_eq_card_basis b', Fintype.card_fin]
  have htn := GlobalTheory.T.adicCompletion_trace_norm_of_basis_image_alt K L v v' f hfK _ (Module.finBasis K L) b' hb'
  have hcont := GlobalTheory.T.adicCompletion_trace_norm_continuous_alt K L v v' f hfc hfd

  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (v'.adicCompletion L) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (Kbar v') :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : IsAlgClosure (v.adicCompletion K) (Kbar v') := ⟨inferInstance, inferInstance⟩
  let b₀ : Kbar v ≃ₐ[v.adicCompletion K] Kbar v' := IsAlgClosure.equiv (v.adicCompletion K) (Kbar v) (Kbar v')
  have hb₀ : ∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) = algebraMap (v'.adicCompletion L) (Kbar v') (f x) :=
    fun x => (b₀.commutes x).trans rfl
  have hint := GlobalTheory.T.residue_closure_iso_ramified_ext K L v v' e f he hfv hfd b₀.toRingEquiv hb₀
  let ι₂ : Ω →ₐ[K] Kbar v :=
    { (b₀.symm.toRingEquiv.toRingHom.comp ι'.toRingHom) with
      commutes' := fun x => by
        change b₀.symm (ι' (algebraMap K Ω x)) = algebraMap K (Kbar v) x
        rw [IsScalarTower.algebraMap_apply K L Ω, ι'.commutes,
          IsScalarTower.algebraMap_apply L (v'.adicCompletion L) (Kbar v'), ← hfK, ← hb₀,
          AlgEquiv.symm_apply_apply, ← IsScalarTower.algebraMap_apply] }
  have hι₂ : IsLocEmb A v ι₂ := fun z => by
    rw [hι' z, hint]
    change IsIntegral _ (ι' z) ↔ IsIntegral _ (b₀ (b₀.symm (ι' z)))
    rw [AlgEquiv.apply_symm_apply]
  obtain ⟨σ, hσ, hσι⟩ := GlobalTheory.T.local_embeddings_differ_by_decomposition K Ω A v ι ι₂ hι hι₂
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.T.decomposition_group_local_galois_iso K Ω A v h ι hι
  let g := θ ⟨σ, hσ⟩
  have hg : ∀ z, g (ι z) = b₀.symm (ι' z) := fun z => (hθ ⟨σ, hσ⟩ z).trans (hσι z).symm
  refine ⟨f, g.toRingEquiv.trans b₀.toRingEquiv, hfc, fun x => ?_, fun z => ?_, hfK, hrank, hcont.1,
    fun z => (htn z).1, hcont.2, fun z => (htn z).2⟩
  · change b₀ (g (algebraMap _ _ x)) = _
    rw [g.commutes, hb₀]
  · change b₀ (g (ι z)) = _
    rw [hg, AlgEquiv.apply_symm_apply]

end
end
end

module

public import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
public import Development.EtaleCohomology.TateTwists.EtaleTwistedCupGradedCommOfFlipAndUniquePairing
public import Development.EtaleCohomology.TateTwists.EtaleTensorTwistedResolutionOfExistenceBoundAndS
public import Development.EtaleCohomology.TateTwists.TwpairTensUnivPf
public import Development.EtaleCohomology.TateTwists.EtaleCochainCupAssocOfCupSpecAndAlexanderWhitney
public import Development.EtaleCohomology.TateTwists.CcCupFlipPf
public import Development.EtaleCohomology.TateTwists.EtaleCupProductNaturalInCoefficients
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsLocallyGenerated
public import Development.EtaleCohomology.TateTwists.EtaleTwistResolutionUniversalExtension
public import Development.EtaleCohomology.TateTwists.EtaleTwistedCupProductAssociative
public import Development.EtaleCohomology.CohomologicalPurity.LeafAWCutTw
public import Development.EtaleCohomology.TateTwists.CcAwFlipPf
public import Development.EtaleCohomology.TateTwists.CupflipEtaDeltaPf
public import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupExistsOfComponents
import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold
public import Development.EtaleCohomology.TateTwists.EtaleComplexAcyclicIffLocalExactness
public import Development.EtaleCohomology.TateTwists.EtaleCupProductFlipExistsOfComponents
public import Development.EtaleCohomology.TateTwists.EtaleRootsOfUnityTwistFlatOfLocalFree
public import Development.EtaleCohomology.TateTwists.EtaleSectionsGlueOverCoverOfComponents
public import Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiIffSectionsOfSeparation
public import Development.EtaleCohomology.TateTwists.EtaleSteenrodWhitneyAlexanderCompatibilityOfComp
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapInjectiveOfSectionsGlu
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorRestrictionAndRootChangeH
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationGeneratorMapOfSectio
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationTensorExistsOfComple
import Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductFamilyOfGluing
import Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyLocalizationBasic
import Development.EtaleCohomology.TateTwists.EtaleTwistedResolutionExistsOfFlatSections
import Development.EtaleCohomology.TateTwists.EtaleSimplexSubfaceComposition
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
import Mathlib.Tactic.Lemma
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
import Development.EtaleCohomology.TateTwists.TAwAssoc0Of
public import Development.EtaleCohomology.TateTwists.TPairAssocPf
import Mathlib.Tactic.Linter.Style
public import Development.EtaleCohomology.TateTwists.TPaTensExPf
public import Development.EtaleCohomology.TateTwists.TPaTensUnivPf
public import Development.EtaleCohomology.TateTwists.EtaleTwistedCupAssocOfTwistedPairingExistsAssoc
import Development.EtaleCohomology.TateTwists.TtResSidePf
public import Development.EtaleCohomology.TateTwists.TtTensExPfSh
public import Development.EtaleCohomology.TateTwists.TtTensPrePf
public import Development.EtaleCohomology.TateTwists.TtTwistSidePf
import Development.EtaleCohomology.TateTwists.TwpairTensUnivExdegPf
public import Development.EtaleCohomology.TateTwists.TwpairZcFunPf
public import Development.EtaleCohomology.TateTwists.TtTensExPf

-- Source module: Development.EtaleCohomology.TateTwists.SubdivisionComposition

section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SubdivisionComposition

lemma subint_comp (N j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l) :
    SimplexCategory.subinterval j' l' h' ≫ SimplexCategory.subinterval j l h =
      SimplexCategory.subinterval (n := N) (j + j') l' (by omega) := by
  ext i
  change ((i : ℕ) + j' + j) = (i : ℕ) + (j + j')
  omega

lemma subint_id (N : ℕ) :
    SimplexCategory.subinterval (n := N) 0 N (by omega) = 𝟙 _ := by
  ext i
  simp [SimplexCategory.subinterval]

lemma along_comp {E : Spc} {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) :
    (x.along a).along b = x.along (b ≫ a) := by
  simp only [Sx.along, op_comp, Functor.map_comp, NatTrans.comp_app, types_comp_apply]

end LateralTheory.EtaleFoundations.SubdivisionComposition

open LateralTheory.EtaleFoundations.SubdivisionComposition in
theorem LateralTheory.EtaleFoundations.simplicial_subinterval_of_subinterval_along_etale : LateralTheory.EtaleFoundations.EtaleSimplexSubfaceComposition := by
  intro E U N x
  have hsa : ∀ (j l : ℕ) (h : j + l ≤ N), x.sub j l h = x.along (SimplexCategory.subinterval j l h) :=
    fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l j' l' h h'
    change (x.along _).along _ = x.along _
    rw [along_comp, subint_comp]
  · rw [hsa, subint_id]
    simp [Sx.along]
  · intro j l h
    refine ⟨?_, ?_, hsa j l h⟩
    · intro V g
      simp only [Sx.sub, Sx.res]
      have hn := ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x
      simp only [ConcreteCategory.comp_apply] at hn
      exact hn
    · intro E' f
      simp only [Sx.sub, Sx.map]
      have hn := congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)
      simp only [NatTrans.comp_app] at hn
      first
        | (have hm := ConcreteCategory.congr_hom hn x
           simp only [ConcreteCategory.comp_apply] at hm
           first | exact hm | exact hm.symm)
        | exact (congrFun hn x).symm
        | (rw [← types_comp_apply, ← hn]; rfl)
  · intro p r a b
    exact along_comp x a b
end
end

-- Source module: Development.EtaleCohomology.TateTwists.TPaCpushHtpyPf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem t_pa_cpush_htpy_of : t_pa_cpush_htpy := by
  intro R _ E I J u u' H n x
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)) =
    CohomologyClass.mk (zcomp α (Cocycle.ofHom u') (add_zero n))
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨α.1.comp (Cochain.ofHomotopy H) (show n + -1 = n - 1 by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  simp [zcomp, Cochain.comp_sub]

end LateralTheory.EtaleFoundations
end
end

-- Source module: Development.EtaleCohomology.TateTwists.TPaCpushIdPf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem t_pa_cpush_id_of : t_pa_cpush_id := by
  intro R _ E I n x
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp a (Cocycle.ofHom (𝟙 I)) (add_zero n)) = CohomologyClass.mk a
  congr 1
  apply Cocycle.ext
  simp [zcomp]

end LateralTheory.EtaleFoundations
end
end

-- Source module: Development.EtaleCohomology.TateTwists.TPaPrecompPf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem pa_sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)
  simpa using this.symm

theorem pa_sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem t_pa_precomp_of : t_pa_precomp := by
  intro R _ I I' J K u μ
  refine ⟨⟨fun U s t w h => (μ.mul U s t w h).comp ((u.f s).hom.app (op U)).hom, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    simp only [LinearMap.comp_apply]
    exact (μ.nat g s t w h _ b).trans (by rw [pa_sec_res_map])
  · intro U s t w h a b
    simp only [LinearMap.comp_apply]
    rw [μ.leibniz]
    congr 2
    rw [← pa_sec_map_comp, u.comm]; rfl
  · intro U s t w h a b
    rfl

end LateralTheory.EtaleFoundations
end
end

-- Source module: Development.EtaleCohomology.TateTwists.TTwpairExPf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleTateTwistCupPairingExistsAndCupUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
      ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem t_twpair_ex_of (htw : EtaleTateTwistCupPairingExistsAndCupUnique) : t_twpair_ex := by
  intro q _ i j
  exact ⟨twPair q i j, (htw q i j).1⟩

end LateralTheory.EtaleFoundations
end
end

-- Source module: Development.EtaleCohomology.TateTwists.TtTensGePf

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0)

theorem tt_tens_ge_of (h : tens_univ_ge) : tt_tens_ge := by
  intro R _ I J K μ hI hJ hμ
  exact h R μ hμ hI hJ

end LateralTheory.EtaleFoundations
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.TwPairExists

section

@[expose] public section

namespace LateralTheory.Fix.CupProductTensor
open LateralTheory.EtaleFoundations

theorem cup_spec0 : t_cup_spec0 := LateralTheory.Fin.EtaleCupProductNaturalInCoefficients.etale_cup_product_compatibility_specification_of_components
theorem cup_assoc0 : EtaleCochainCupAssociativeOfPairing :=
  etale_cochain_cup_assoc_of_cup_spec_and_alexander_whitney_assoc cup_spec0 (t_aw_assoc0_of etale_chain_cochain_eval_basic_properties_hold simplicial_subinterval_of_subinterval_along_etale)
theorem secSep : EtaleTensorTripleProductLeibnizSeparated.SecSep := etale_sheaf_sections_separated_holds
theorem tens_tri : EtaleTensorPairProductAssociative :=
  etale_tensor_triple_product_of_family_and_leibniz (etale_tensor_triple_product_family_of_gluing LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange)
    (etale_tensor_triple_product_leibniz_of_separated secSep)
theorem tens_ex : tt_tens_ex := tt_tens_ex_of tt_tens_pre_of etale_presheaf_tensor_data_sheafification_is_tensor_complex
theorem univ_exdeg : twpair_tens_univ_exdeg := twpair_tens_univ_exdeg_of
theorem tens_univ : twpair_tens_univ := twpair_tens_univ_of univ_exdeg
theorem tens_ge : tt_tens_ge := tt_tens_ge_of (by intro R _ I J K τ hτ; exact (tens_univ R τ hτ).2.1)
theorem res_side : tt_res_side := tt_res_side_of tens_univ LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange
theorem twres_ext : EtaleTwistResolutionUniversalExtension := LateralTheory.Fin.EtaleTwistResolutionUniversalExtension.intersectionNumber_baseChange
theorem cup_compat : EtaleCupProductNaturalInCoefficients := LateralTheory.Fin.EtaleCupProductNaturalInCoefficients.intersectionNumber_baseChange

theorem holds_of (hts : EtaleTateTwistSectionsLocallyGenerated) :
    EtaleTwistedCupProductAssociative ∧ EtaleTwistResolutionPairingCupUnique := by
  have hsec : TwMulGenMap.twSec := hts
  have hloc : EtaleTateTwistSectionsLocallyMultiplesOfGenerator := fun q _ i => (hts q i).1
  have hinj : EtaleTateTwistGeneratorMapSectionsInjective := etale_tate_twist_generator_map_injective_of_sections_glue hts LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
    LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange
  have tw_mul : EtaleTateTwistSingletonTensorGenMul := etale_tate_twist_tensor_iso_of_generator_map_iso (etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists tens_ex) (etale_tate_twist_multiplication_generator_map_of_section_description hsec)
    (etale_tate_twist_generator_map_isIso_of_inj_surj etale_sheaf_mono_epi_iff_sections_of_separation (etale_tate_twist_generator_map_surjective_of_local_and_root hloc
      etale_tate_twist_generator_restriction_and_root_change_holds) hinj)
  have twist : tt_twist_side := tt_twist_side_of tw_mul LateralTheory.Fin.EtaleTateTwistSheafFlat.intersectionNumber_baseChange LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange
    LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange
  have twres : EtaleTensorPairTwistResolutionMul := etale_tensor_twisted_resolution_of_existence_bound_and_sides tens_ex tens_ge twist res_side
  have pa : t_pair_assoc := t_pair_assoc_of twres tens_tri twres_ext cup_compat cup_assoc0 t_pa_tens_ex_of
    t_pa_tens_univ_of t_pa_precomp_of t_pa_cpush_id_of t_pa_cpush_htpy_of
  have tp : EtaleTwistResolutionPairingCupUnique := etale_tate_twist_cup_pairing_of_tensor_and_resolution_properties tens_ex tens_univ twres twres_ext cup_compat twpair_zc_fun_of
  exact ⟨etale_twisted_cup_assoc_of_twisted_pairing_exists_assoc (t_twpair_ex_of tp) pa, tp⟩

theorem ringAssoc : LateralTheory.E.CupProductRingLaws.LeafRingAssoc := (holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).1
theorem cupSpec : LateralTheory.E.CupProductRingLaws.LeafCupSpec := fun R _ _ _ _ μ E _ _ _ hk => cup_spec0 R μ (E := E) hk
theorem ringComm (hf : cc_cup_flip) : LateralTheory.E.CupProductRingLaws.LeafRingComm :=
  etale_twisted_cup_graded_comm_of_flip_and_unique_pairing hf (fun R _ _ _ _ μ => (LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange R μ).imp fun _ h => h.1) (holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).2
theorem awFlip : cc_aw_flip := cc_aw_flip_of LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy.intersectionNumber_baseChange cupflip_eta_delta_of

theorem cupFlip : cc_cup_flip := by
  intro R _ I J K μ ν hf E n m k h h' a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (cupSpec R μ E h).1 α β
  obtain ⟨γ', hγ'⟩ := (cupSpec R ν E h').1 β α
  rw [(cupSpec R μ E h).2 _ _ _ hγ, (cupSpec R ν E h').2 _ _ _ hγ']
  exact awFlip R μ ν hf E h h' α β γ γ' hγ hγ'
theorem ringComm' : LateralTheory.E.CupProductRingLaws.LeafRingComm := ringComm cupFlip
theorem twPairExists : LateralTheory.E.CupProductRingLaws.LeafTwPairExists := fun q _ i j => ⟨_, ((holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).2 q i j).1⟩
end LateralTheory.Fix.CupProductTensor
end
end

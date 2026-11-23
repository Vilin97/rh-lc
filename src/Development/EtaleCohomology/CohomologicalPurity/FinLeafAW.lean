module

public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
public import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsLocallyGenerated
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistSingletonTensorGenMul
public import Development.EtaleCohomology.TateTwists.EtaleTensorCyclesLocallyLiftOfRowExactAndDescent
public import Development.EtaleCohomology.TateTwists.EtaleTensorPairQuasiIsoOfFlatQuasiIso
public import Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPf
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
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
public import Development.EtaleCohomology.EtaleSheaves.LeafTwTensExPf
public import Development.EtaleCohomology.TateTwists.EtaleTensorPairTwistResolutionMul
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Development.EtaleCohomology.KummerTheory.CupAWCut
public import Development.EtaleCohomology.TateTwists.ColumnOf
public import Development.EtaleCohomology.TateTwists.EtaleCupProductFlipExistsOfComponents
public import Development.EtaleCohomology.TateTwists.EtaleRootsOfUnityTwistFlatOfLocalFree
public import Development.EtaleCohomology.TateTwists.EtaleSectionsGlueOverCoverOfComponents
public import Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiIffSectionsOfSeparation
public import Development.EtaleCohomology.TateTwists.EtaleShortComplexExactIffLocallySurjectiveOnKernel
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapInjectiveOfSectionsGlu
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistLocalGenerationAndRootCompatOfPart
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationGeneratorMapOfSectio
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationTensorExistsOfComple
public import Development.EtaleCohomology.TateTwists.EtaleTensorComplexUniversalOfDegreewise
public import Development.EtaleCohomology.TateTwists.EtaleTensorCycleLocallyLowersTopDegreeOfRowExact
public import Development.EtaleCohomology.TateTwists.EtaleTensorProductSheafExistsOfComponents
public import Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyLocalizationBasic
public import Development.EtaleCohomology.TateTwists.EtaleTwistedResolutionExistsOfFlatSections
public import Development.EtaleCohomology.TateTwists.TtResSidePf
public import Development.EtaleCohomology.TateTwists.TtTwistSidePf
public import Development.EtaleCohomology.TateTwists.acycIffPf
public import Development.EtaleCohomology.TateTwists.conePf
public import Development.EtaleCohomology.TateTwists.EtaleTensorTwistedResolutionOfExistenceBoundAndS
public import Development.EtaleCohomology.CohomologicalPurity.LeafAWCutTw

-- Source module: Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPfExt

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairExistsPf

variable (q : ℕ) (k : ℤ)

instance resKInj : (res (ZMod q) (tw q k)).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem ext_homotopy {S T L : Cx (ZMod q)} (ε : S ⟶ T) [QuasiIso ε] (a : S ⟶ L) [L.IsKInjective] :
    ∃ u : T ⟶ L, Nonempty (Homotopy (ε ≫ u) a) := by
  let _ := HasDerivedCategory.standard (Shv (ZMod q))
  let Φ := DerivedCategory.quotientCompQhIso (Shv (ZMod q))
  obtain ⟨g, hg⟩ := (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj T) L).2
    (Φ.hom.app T ≫ inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map a ≫ Φ.inv.app L)
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨u, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj S) L).1
  have nat : ∀ {X Y : Cx (ZMod q)} (f : X ⟶ Y), DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) =
      Φ.hom.app X ≫ DerivedCategory.Q.map f ≫ Φ.inv.app Y := by
    intro X Y f
    have := Φ.hom.naturality f
    simp only [Functor.comp_map] at this
    rw [← Category.assoc, ← this]
    simp
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (ε ≫ u)) = _
  rw [Functor.map_comp, Functor.map_comp, hg, nat ε, nat a]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id_assoc]

theorem leafTwResExt : LeafTwResExt := by
  intro q _ k T e ⟨_, ε, hε, he⟩
  obtain ⟨u, ⟨H⟩⟩ := ext_homotopy q (ε := ε) (a := resAug (tw q k))
  refine ⟨u, fun U ζ => ?_⟩
  have h0 : ε.f 0 ≫ u.f 0 = (resAug (tw q k)).f 0 := by
    have hc := H.comm 0
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hc
    have z1 : IsZero ((sgl (tw q k)).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
    have z2 : IsZero ((res (ZMod q) (tw q k)).X (-1)) := by
      unfold res InjectiveResolution.cochainComplex
      exact HomologicalComplex.isZero_extend_X _ _ _ (by
        intro n hn
        change ((n : ℕ) : ℤ) = -1 at hn
        omega)
    have e1 : H.hom 1 0 = 0 := z1.eq_of_src _ _
    have e2 : H.hom 0 (-1) = 0 := z2.eq_of_tgt _ _
    rw [e1, e2] at hc
    simpa using hc
  rw [← he U ζ, map_map, map_map, h0]
  rfl

theorem LeafTwPairExists_of' (h1 : LeafTwTensEx) (h2 : LeafTwTensRes) : LateralTheory.E.CupProductRingLaws.LeafTwPairExists :=
  LeafTwPairExists_of h1 h2 leafTwResExt

end LateralTheory.E.LeafTwPairExistsPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.LeafTwTensResPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwTensResPf

def LeafTensTwres : Prop := LateralTheory.EtaleFoundations.EtaleTensorPairTwistResolutionMul

def LeafResFlat : Prop := ∀ (q : ℕ) [NeZero q] (j t : ℤ), FlatS ((res (ZMod q) (tw q j)).X t)

instance resGE (q : ℕ) (i : ℤ) : (res (ZMod q) (tw q i)).IsStrictlyGE 0 := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem res_isTwRes (q : ℕ) [NeZero q] (i : ℤ) :
    IsTwRes q i (res (ZMod q) (tw q i)) (fun _ ζ => resGen i ζ) := by
  refine ⟨resGE q i, resAug (tw q i), ?_, fun U ζ => ?_⟩
  · unfold resAug
    exact (inferInstance : QuasiIso (injectiveResolution (tw q i)).ι')
  · simp only [resGen, resι, sglι, Sec.map]
    rfl

theorem leafTwTensRes_of (h1 : LeafTensTwres) (h2 : LeafResFlat) : LateralTheory.E.LeafTwPairExistsPf.LeafTwTensRes := by
  intro q _ i j T τ hτ
  exact h1 q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) (res_isTwRes q i) (res_isTwRes q j) (h2 q j) τ hτ

end LateralTheory.E.LeafTwTensResPf
end
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafAWCut

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.EtaleFoundations

namespace LateralTheory.CohomologicalPurity.LeafAWCut

def LeafTwSec : Prop := EtaleTateTwistSectionsLocallyGenerated

theorem of_pair (h : LateralTheory.E.CupProductRingLaws.LeafTwPairExists) : LateralTheory.CohomologicalPurity.LeafAW := by
  intro q _ i j
  exact ⟨pick_spec (h q i j), fun E n m α β => LateralTheory.KummerTheory.CupAW_of (ZMod q) (twPair q i j) E rfl α β⟩

theorem row : EtaleTensorWithFlatPreservesLocalExactness := by
  intro R _ C J hJ hC s t V x hx
  have hA : C.Acyclic := fun n => (etale_short_complex_exact_iff_locally_surjective_on_kernel R (C.sc n)).2 (hC n)
  exact acyc.column_of R C J hJ ((acyc.acycIff_of R C).1 hA) V s t x hx

theorem tensAcyc : EtaleTensorAcyclicOfFlatBounded :=
  etale_tensor_complex_acyclic_of_locally_exact_flat etale_short_complex_exact_iff_locally_surjective_on_kernel (etale_tensor_complex_locally_exact_of_lifted_sections
    (etale_tensor_cycles_locally_lift_of_row_exact_and_descent row etale_tensor_cycle_locally_lowers_top_degree_of_row_exact))

theorem tensQis : EtaleTensorPairQuasiIsoOfFlatQuasiIso := etale_tensor_preserves_quasiIso_of_acyclic_and_cone tensAcyc tqis.cone_of

theorem pair_of (hq : EtaleTensorPairQuasiIsoOfFlatQuasiIso) (hm : EtaleTateTwistSingletonTensorGenMul) : LateralTheory.E.CupProductRingLaws.LeafTwPairExists :=
  LateralTheory.E.LeafTwPairExistsPf.LeafTwPairExists_of' LateralTheory.E.LeafTwTensExPf.LeafTwTensEx_of
    (LateralTheory.E.LeafTwTensResPf.leafTwTensRes_of
      (etale_tensor_twisted_resolution_of_existence_bound_and_sides LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange
        (fun R _ _ _ _ μ hI hJ hμ => (LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange R μ hμ).2.1 hI hJ)
        (tt_twist_side_of hm LateralTheory.Fin.EtaleTateTwistSheafFlat.intersectionNumber_baseChange LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange hq)
        (tt_res_side_of LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange hq))
      (fun q _ j t => (LateralTheory.Fin.EtaleTwistResolutionUniversalExtension.intersectionNumber_baseChange q j).2.1 t))

theorem twMul (hT : LeafTwSec) : EtaleTateTwistSingletonTensorGenMul :=
  etale_tate_twist_tensor_iso_of_generator_map_iso (etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange) (etale_tate_twist_multiplication_generator_map_of_section_description hT)
    (etale_tate_twist_generator_map_isIso_of_inj_surj etale_sheaf_mono_epi_iff_sections_of_separation
      (etale_tate_twist_generator_map_surjective_of_local_and_root (fun q _ i => (hT q i).1)
        (fun q _ j => ⟨(hT q j).2.2.2.1, fun U ζ ξ => (hT q j).2.1 U ζ (twGen j ξ)⟩))
      (etale_tate_twist_generator_map_injective_of_sections_glue hT LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange))

theorem goal_of (h2 : LeafTwSec) : LateralTheory.CohomologicalPurity.LeafAW :=
  of_pair (pair_of tensQis (twMul h2))

end LateralTheory.CohomologicalPurity.LeafAWCut
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.LeafAWCutFin

section

@[expose] public section

theorem LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of : LateralTheory.CohomologicalPurity.LeafAW :=
  LateralTheory.CohomologicalPurity.LeafAWCut.goal_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec
end
end

-- Source module: Development.EtaleCohomology.CohomologicalPurity.FinLeafAW

section

@[expose] public section

namespace LateralTheory.Fin.LeafAW
theorem etale_purity_aw : LateralTheory.CohomologicalPurity.LeafAW := by
  apply LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafAW := etale_purity_aw
end LateralTheory.Fin.LeafAW
end
end

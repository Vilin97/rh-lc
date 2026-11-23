module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicExtendScalarsZmodOfFlatBoundedBelowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafBiprodStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafIsoAndZeroStatement
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlatStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsZmodOfFlatResolution

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedQis

theorem quasiIso_of_cone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

theorem flatS_cone {R : Type} [CommRing R] (F : Shv R) (hF : FlatS F) (T : Cx R) (hT : ∀ t, FlatS (T.X t))
    (ε : sgl F ⟶ T) (n : ℤ) : FlatS ((mappingCone ε).X n) := by
  obtain ⟨hiso, hzero⟩ := GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero R
  refine hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod ε n (n + 1) rfl).symm
    (GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod _ _ _ ?_ (hT n))
  by_cases h : n + 1 = 0
  · exact hiso (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 F (n + 1) h).symm hF
  · exact hzero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

theorem quasiIso_extCx_of_flat : ∀ (Q q : ℕ) [NeZero Q] (h : q ∣ Q) (F : Shv (ZMod Q)) (T : Cx (ZMod Q))
    [T.IsStrictlyGE 0], FlatS F → (∀ t, FlatS (T.X t)) → ∀ ε : sgl F ⟶ T, QuasiIso ε →
    QuasiIso ((GlobalTheory.EtC.ScalarExt.extCx (ZMod.castHom h (ZMod q))).map ε) := by
  intro Q q _ h F T _ hF hT ε hε
  have hK : (mappingCone ε).Acyclic := GlobalTheory.mappingCone_acyclic_of_quasiIso _
  have hNeg : (-1 : ℤ) < 0 := neg_one_lt_zero
  have hBound := CochainComplex.isStrictlyGE_mappingCone ε 0 0 (-1) hNeg (Int.le_of_lt hNeg)
  have hE := @GlobalTheory.T.acyclic_extendScalars_zmod_of_flat_boundedBelow Q q _ h
    (mappingCone ε) (-1) hBound (flatS_cone F hF T hT ε) hK
  have hC : (mappingCone (((extSh (ZMod.castHom h (ZMod q))).mapHomologicalComplex _).map ε)).Acyclic := fun n =>
    (hE n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso ε (extSh (ZMod.castHom h (ZMod q))))
  exact quasiIso_of_cone_acyclic _ hC

end GlobalTheory.EtC.RedQis

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsZmodOfFlatResolutionStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.quasiIso_extendScalars_zmod_of_flat_resolution : ∀ (Q q : ℕ) [NeZero Q] (h : q ∣ Q) (F : Shv (ZMod Q)) (T : Cx (ZMod Q)) [T.IsStrictlyGE 0], FlatS F → (∀ t, FlatS (T.X t)) → ∀ ε : sgl F ⟶ T, QuasiIso ε → QuasiIso ((GlobalTheory.EtC.ScalarExt.extCx (ZMod.castHom h (ZMod q))).map ε) := by
  first | exact @GlobalTheory.EtC.RedQis.quasiIso_extCx_of_flat | exact GlobalTheory.EtC.RedQis.quasiIso_extCx_of_flat | (intros; apply GlobalTheory.EtC.RedQis.quasiIso_extCx_of_flat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiMapEqOfFlatTateTwistResolution

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ScalarExt

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP0⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hP0 V g hg)⟩

theorem agree_on_twist {Q q : ℕ} [NeZero Q] (k : ℤ) {T : Cx (ZMod Q)} {J : Cx (ZMod q)} (ε : sgl (tw Q k) ⟶ T)
    (σ σ' : SemiMap T J)
    (he : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) =
      σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))))
    (U : Scheme.{0}) (y : Sec (tw Q k) U) :
    σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) y)) = σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) y)) := by
  refine ((GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (J.X 0) U).1 _ _ (loc_mono ((GlobalTheory.T.tateTwist_sections_locally_generated Q k).1 U y) fun V g hg => ?_))
  rw [σ.nat, σ'.nat, sec_map_res, sec_map_res]
  rcases hg with h0 | ⟨ζ, c, hc⟩
  · rw [h0]; simp
  · have hm : ∀ {A B : Shv (ZMod Q)} (φ : A ⟶ B) (x : Sec A V), Sec.map φ (c • x) = c • Sec.map φ x :=
      fun φ x => map_nsmul (φ.hom.app (op V)).hom c x
    rw [hc, hm, hm, map_nsmul, map_nsmul, he]

end GlobalTheory.EtC.ScalarExt

namespace GlobalTheory.EtC.ScalarExt

theorem semiMap_op_eq_of_flat_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  intro Q q _ h k T e hT hflat σ σ' hσ E n x
  obtain ⟨hge, ε, hqi, hεe⟩ := hT
  haveI := hge
  have hl := zmod_semilinear h σ
  have hl' := zmod_semilinear h σ'
  let εb : sgl ((ext (ZMod.castHom h (ZMod q))).obj (tw Q k)) ⟶ (extCx (ZMod.castHom h (ZMod q))).obj T :=
    ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv ≫ (extCx (ZMod.castHom h (ZMod q))).map ε
  have hq2 : QuasiIso ((extCx (ZMod.castHom h (ZMod q))).map ε) :=
    GlobalTheory.T.quasiIso_extendScalars_zmod_of_flat_resolution Q q h (tw Q k) T (GlobalTheory.T.tateTwistSheaf_isLocallyFlat Q k) hflat ε hqi
  haveI : IsIso ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv := Iso.isIso_inv _
  have hq1 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (ext (ZMod.castHom h (ZMod q))) (ComplexShape.up ℤ) 0).app
      (tw Q k)).inv := quasiIso_of_isIso _
  haveI : QuasiIso εb := quasiIso_comp (hφ := hq1) (hφ' := hq2) _ _
  haveI : (res (ZMod q) (tw q k)).IsKInjective :=
    inferInstanceAs ((injectiveResolution (tw q k)).cochainComplex.IsKInjective)
  haveI : (res (ZMod q) (tw q k)).IsStrictlyGE 0 :=
    inferInstanceAs ((injectiveResolution (tw q k)).cochainComplex.IsStrictlyGE 0)
  haveI : IsIso (sglι (tw Q k)) := by unfold sglι; exact Iso.isIso_inv _
  have he : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) =
      σ'.app U 0 (Sec.map (ε.f 0) (Sec.map (sglι (tw Q k)) (twGen k ζ))) := fun U ζ => by
    rw [hεe]; exact hσ U ζ
  have hcomp : εb ≫ semiBar σ hl = εb ≫ semiBar σ' hl' := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = 0
    · subst hi
      have key : (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ (semiBar σ hl).f 0 =
          (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ (semiBar σ' hl').f 0 := by
        change (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ ((adj _).homEquiv _ _).symm (semiHom σ hl 0) =
          (ext (ZMod.castHom h (ZMod q))).map (ε.f 0) ≫ ((adj _).homEquiv _ _).symm (semiHom σ' hl' 0)
        rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_left_symm]
        congr 1
        rw [← cancel_epi (sglι (tw Q k))]
        ext U y
        exact agree_on_twist k ε σ σ' he U.unop y
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      dsimp only [εb]
      erw [HomologicalComplex.comp_f, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) key
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
  obtain ⟨H⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) _ _ _ εb).2 _ _ hcomp
  have h1 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective (ZMod Q) (ZMod q) (unitSemi T) σ (semiBar σ hl) (semi_factor σ hl)).1 E n x
  have h2 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective (ZMod Q) (ZMod q) (unitSemi T) σ' (semiBar σ' hl') (semi_factor σ' hl')).1 E n x
  rw [h1, h2, ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)).2.2.2.2 _ _ ⟨H⟩ _ n).2]

end GlobalTheory.EtC.ScalarExt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiMapEqOfFlatTateTwistResolutionStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  first | (exact @GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (exact GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (intros; apply GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res  <;> assumption)
end
end

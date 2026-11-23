module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleRationalLocalUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValuesDetOmegaDeltaLocalUnits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUniformisedFourierFrameAbsOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCancelPulledBundlesGermsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledIsoPreservingRigidificationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTransportAlongGeneratingIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoPreservesRigidificationAtOriginStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMapsSecPullOfPointwiseGermsStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitUniformisedOfAbsValueOneStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValuesDetOmegaDeltaLocalUnitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.thetaKeyValues_detOmega_delta_local_units : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  first | exact @GlobalTheory.KeyValsPf.keyVals | exact GlobalTheory.KeyValsPf.keyVals | (intros; apply GlobalTheory.KeyValsPf.keyVals <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnits

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenGlue

theorem lbPow_U' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j : (lbPow M n).ι) : (lbPow M n).U j = M.U (j PUnit.unit) := by
  ext x
  simp only [lbPow, LB.LinComb, LB.wchart]
  simp
  exact ⟨fun h => h _, fun h i => h⟩

theorem germ_lbPow_g' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j j' : (lbPow M n).ι) (x : S)
    (h : x ∈ (lbPow M n).U j ⊓ (lbPow M n).U j') (h' : x ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :
    S.presheaf.germ _ x h ((lbPow M n).g j j' : Γ(S, (lbPow M n).U j ⊓ (lbPow M n).U j')) =
      S.presheaf.germ _ x h' (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(S, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) ^ n := by
  simp only [lbPow, LB.LinComb, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  congr 1
  simp [res, pullU]
  erw [map_pow]
  congr 1
  erw [Units.coe_map, Units.coe_map]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem keyGlob_of_keyLoc : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → KeyGlob := by
  intro κ hH hF hL S s G _ _ g L δ σ hg hS hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  haveI := hS
  obtain ⟨f, hloc, hcomp⟩ := GlobalTheory.T.thetaKeyValues_detOmega_delta_local_units κ hH hF hL S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  refine GlobalTheory.T.lineBundleIso_of_compatible_rational_local_units S (lbPow δ 8) (lbPow (SiegelTor.hodge G g) 4) (fun p => f (p.1 PUnit.unit) (p.2 PUnit.unit)) ?_ ?_
  · rintro ⟨c, i⟩ x hx
    rw [lbPow_U', lbPow_U'] at hx
    obtain ⟨V, hV, hxV, u, hu⟩ := hloc _ _ x hx
    exact ⟨V, by rw [lbPow_U', lbPow_U']; exact hV, hxV, u, hu⟩
  · rintro ⟨c, i⟩ ⟨c', i'⟩ h1 h2
    have h1' : genericPoint S ∈ (VB.det (LieVB.omega G) g).U (c PUnit.unit) ⊓ (VB.det (LieVB.omega G) g).U (c' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h1; exact h1
    have h2' : genericPoint S ∈ δ.U (i PUnit.unit) ⊓ δ.U (i' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h2; exact h2
    dsimp only
    rw [germ_lbPow_g' δ 8 i i' _ h2 h2', germ_lbPow_g' _ 4 c c' _ h1 h1']
    exact hcomp _ _ _ _ h1' h2'

end GlobalTheory.KeyEvenGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.key_formula_even_degeneration_global_of_local_units : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → KeyGlob := by
  first | exact @GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc | exact GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc | (intros; apply GlobalTheory.KeyEvenGlue.keyGlob_of_keyLoc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyFormulaUnitOverNormalBase_of_familyUnit_of_traits : ∀ κ : Rule, FamUnit κ → KeyTrait κ → KeyLoc κ := by
  first | exact @GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait | exact GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait | (intros; apply GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitTraitsOfUniformisedTraits

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven

theorem dualMapR_eq_of_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h1 : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun a => ?_
  have hx : ∀ (S : Type) [CommRing S] (b : DualNumber S),
      b = algebraMap S (DualNumber S) (TrivSqZeroExt.fst b) + algebraMap S (DualNumber S) (TrivSqZeroExt.snd b) * DualNumber.eps := by
    intro S _ b
    rw [← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl,
      TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  have hF : F a = algebraMap R' (DualNumber R') (f (TrivSqZeroExt.fst a)) +
      algebraMap R' (DualNumber R') (f (TrivSqZeroExt.snd a)) * DualNumber.eps := by
    conv_lhs => rw [hx R a]
    rw [map_add (f := _), map_mul, h1, h1, h2]
  rw [hF, ← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

theorem keyTrait_of_keyTraitU : ∀ κ : Rule, KeyTraitU κ → KeyTrait κ := by
  intro κ hU V _ _ _ _ hA hF G _ _ L σ x y hSA hUn hLie hNz hKey
  obtain ⟨D, A, U, e, he⟩ := hUn
  obtain ⟨φ, hφe, ψ, F, hPB, hψ, hRig, hTh, hF1, hF2, hv⟩ := hKey
  obtain ⟨θ, hθm, hθφ⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hPB

  obtain ⟨e', he', heR⟩ := GlobalTheory.T.exists_rescaled_iso_preserving_rigidification G U.LG L e he
  obtain ⟨σ', hσ', hnz⟩ := GlobalTheory.T.exists_section_transport_along_generating_iso e' he' U.LG.isLB L.isLB σ
  obtain ⟨w₀, hw₀, hPW⟩ := GlobalTheory.T.exists_iso_cancel_pulled_bundles_germs θ.hom.left φ (pullback.fst G.hom (jK V)) hθφ x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB ψ e' hψ he'
  let U' : Unif (IsLocalRing.maximalIdeal V) D x.P G :=
    { toUnifPre := { U.toUnifPre with gen := θ, gen_hom := hθm, ext := ⟨w₀, hw₀⟩ }, expand := U.expand }
  have hinv : U'.gen.inv.left ≫ pullback.fst G.hom (jK V) = φ := by
    show θ.inv.left ≫ pullback.fst G.hom (jK V) = φ
    rw [← hθφ, ← Category.assoc, ← Over.comp_left, θ.inv_hom_id, Over.id_left, Category.id_comp]
  have hFd := dualMapR_eq_of_map _ F hF1 hF2
  haveI : IsMonHom θ.hom := hθm
  refine hU V hA hF D x G hSA U' w₀ ⟨hw₀, x.rig_gen, ?_⟩ y hLie (fun i => ?_) σ' ?_ ?_
  · exact GlobalTheory.T.iso_preserves_rigidification_at_origin V G x.P.A θ.hom φ hθφ hφe x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB x.rig L.rig U.LG.rig ψ e' w₀ hPW hRig heR
  · show (x.v i).left ≫ (U'.gen.inv.left ≫ pullback.fst G.hom (jK V)) = _
    rw [hinv, hv i, hFd]
  · intro s
    obtain ⟨z, hz, hz'⟩ := hNz s
    exact ⟨z, hz, hnz hz'⟩
  · exact GlobalTheory.T.secMaps_secPull_of_pointwise_germs θ.hom.left φ _ hθφ x.P.L L.L U.LG.L L.isLB ψ e' w₀ hPW x.th σ σ' hTh hσ'

end GlobalTheory.KeyEven

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitTraitsOfUniformisedTraitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyValue_unit_traits_of_uniformised_traits : ∀ κ : Rule, KeyTraitU κ → KeyTrait κ := by
  first | exact @GlobalTheory.KeyEven.keyTrait_of_keyTraitU | exact GlobalTheory.KeyEven.keyTrait_of_keyTraitU | (intros; apply GlobalTheory.KeyEven.keyTrait_of_keyTraitU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenClosing

theorem keyGlob : KeyGlob := by
  obtain ⟨κ, hH, hF, -, hT, -, hU, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have h4 : MBLow.Rule4 κ := ⟨hH, hF, hT, hU⟩
  exact GlobalTheory.T.key_formula_even_degeneration_global_of_local_units κ hH hF (GlobalTheory.T.keyFormulaUnitOverNormalBase_of_familyUnit_of_traits κ hU (GlobalTheory.T.keyValue_unit_traits_of_uniformised_traits κ (GlobalTheory.T.keyValue_unit_uniformised_of_absValueOne κ (GlobalTheory.T.key_value_uniformised_fourier_frame_abs_one κ h4))))

end GlobalTheory.KeyEvenClosing
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyFormula_evenDegeneration_global : KeyGlob := by
  first | exact @GlobalTheory.KeyEvenClosing.keyGlob | exact GlobalTheory.KeyEvenClosing.keyGlob | (intros; apply GlobalTheory.KeyEvenClosing.keyGlob <;> assumption)
end
end

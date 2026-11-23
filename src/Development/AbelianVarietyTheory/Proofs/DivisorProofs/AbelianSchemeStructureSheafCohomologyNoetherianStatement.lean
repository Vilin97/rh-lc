module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecialFibreCohomologyLiftArtinianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyStructureSheafCohomologyAnyFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroAbelianH1Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibreStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfResidueFieldFibres
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePropertyFromFibres

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.Wedge

def alt2 {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) : M [⋀^Fin 2]→ₗ[R] N where
  toFun v := f (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all

theorem alt2_apply {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) (v : Fin 2 → M) : alt2 f hf v = f (v 0) (v 1) := rfl

theorem bijective_of_fibres {R B C : Type} [CommRing R] [AddCommGroup B] [Module R B] [AddCommGroup C]
    [Module R C] [Module.Finite R B] [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ q : PrimeSpectrum R, Function.Bijective (l.baseChange q.asIdeal.ResidueField)) :
    Function.Bijective l := by
  have hlt : ∀ q : PrimeSpectrum R, Function.Bijective (l.lTensor q.asIdeal.ResidueField) := by
    intro q
    have e : ⇑(l.lTensor q.asIdeal.ResidueField) = ⇑(l.baseChange q.asIdeal.ResidueField) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    rw [e]; exact h q
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective l
      (fun m hm => (hlt ⟨m, hm.isPrime⟩).1)
    exact Function.LeftInverse.injective (g := r) fun x => LinearMap.congr_fun hr x
  · have hQ : Subsingleton (C ⧸ LinearMap.range l) := by
      apply GlobalTheory.subsingleton_of_residueField_fibres R
      intro q
      have h2 := (hlt q).2
      have h3 : Function.Surjective ((LinearMap.range l).mkQ.lTensor q.asIdeal.ResidueField) :=
        LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
      refine ⟨fun a b => ?_⟩
      have key : ∀ a : q.asIdeal.ResidueField ⊗[R] (C ⧸ LinearMap.range l), a = 0 := by
        intro a
        obtain ⟨x, rfl⟩ := h3 a
        obtain ⟨y, rfl⟩ := h2 x
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.range_mkQ_comp]
        simp
      rw [key a, key b]
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    exact hQ

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

def wedgeMap (hsq : ∀ x : HO1 s, cup _ x x = 0) : ⋀[R]^2 (HO1 s) →ₗ[R] HO2 s :=
  exteriorPower.alternatingMapLinearEquiv (alt2 (cup _) hsq)

theorem wedgeMap_ιMulti (hsq : ∀ x : HO1 s, cup _ x x = 0) (v : Fin 2 → HO1 s) :
    wedgeMap s hsq (exteriorPower.ιMulti R 2 v) = cup _ (v 0) (v 1) := by
  simp only [wedgeMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, alt2_apply]

theorem baseChange_wedgeMap_bijective (hsq : ∀ x : HO1 s, cup _ x x = 0) (k : Type) [CommRing k]
    [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X)
    (hpb : φ ≫ s = s' ≫ spMap (algebraMap R k))
    (e1 : k ⊗[R] HO1 s ≃ₗ[k] HO1 s') (he1 : ∀ c, e1 (1 ⊗ₜ c) = pullHO1 hpb c)
    (e2 : k ⊗[R] HO2 s ≃ₗ[k] HO2 s') (he2 : ∀ c, e2 (1 ⊗ₜ c) = pullHO2 hpb c)
    (w : ⋀[k]^2 (CatCoh.H1 (OAff s')) ≃ₗ[k] CatCoh.H2 (OAff s'))
    (hw : ∀ a b, w (exteriorPower.ιMulti k 2 ![a, b]) = cup _ a b) :
    Function.Bijective ((wedgeMap s hsq).baseChange k) := by
  have hcup := ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 R k X X' s s' (algebraMap R k) φ hpb).1
  let β := (GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange R (HO1 s) k) 2).equiv
  let T : k ⊗[R] ⋀[R]^2 (HO1 s) →ₗ[k] k ⊗[R] HO2 s :=
    e2.symm.toLinearMap ∘ₗ w.toLinearMap ∘ₗ exteriorPower.map 2 e1.toLinearMap ∘ₗ β.toLinearMap
  have hT : T = (wedgeMap s hsq).baseChange k := by
    refine TensorProduct.AlgebraTensorModule.ext fun c x => ?_
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    have hl : (T.restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 =
        (((wedgeMap s hsq).baseChange k).restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 := by
      apply exteriorPower.linearMap_ext
      ext v
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearMap.baseChange_tmul,
        wedgeMap_ιMulti, T, LinearEquiv.coe_coe, β, IsBaseChange.equiv_tmul, one_smul,
        GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.map_apply_ιMulti]
      have hv : (⇑e1 ∘ fun i => (1 : k) ⊗ₜ[R] v i) = ![pullHO1 hpb (v 0), pullHO1 hpb (v 1)] := by
        funext i; fin_cases i <;> simp [he1]
      rw [hv, hw, LinearEquiv.symm_apply_eq, he2, hcup]
    exact LinearMap.congr_fun hl x
  rw [← hT]
  have hm : Function.Bijective (exteriorPower.map 2 e1.toLinearMap) := by
    refine Function.bijective_iff_has_inverse.2 ⟨exteriorPower.map 2 e1.symm.toLinearMap, ?_, ?_⟩
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
  exact e2.symm.bijective.comp (w.bijective.comp (hm.comp β.bijective))

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

theorem wedgeO_of_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Module.Finite R (HO1 s) → Module.Projective R (HO1 s) → Module.Finite R (HO2 s) → Module.Projective R (HO2 s) → StructureSheafH1BaseChange s → StructureSheafH2BaseChange s → (∀ x : HO1 s, cup _ x x = 0) → (∀ (k : Type) [Field k] [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R k))), WedgeO (OAff s')) → WedgeO (OAff s) := by
  intro R _ X s hF1 hP1 hF2 hP2 hB1 hB2 hsq hfib
  have hbij : Function.Bijective (wedgeMap s hsq) := by
    refine bijective_of_fibres _ fun q => ?_
    obtain ⟨X', s', φ, hpb⟩ : ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp q.asIdeal.ResidueField) (φ : X' ⟶ X),
        IsPullback φ s' s (spMap (algebraMap R q.asIdeal.ResidueField)) :=
      ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
    obtain ⟨e1, he1⟩ := hB1 _ _ _ _ hpb
    obtain ⟨e2, he2⟩ := hB2 _ _ _ _ hpb
    obtain ⟨w, hw⟩ := hfib _ _ _ _ hpb
    exact baseChange_wedgeMap_bijective s hsq _ X' s' φ hpb.w e1 he1 e2 he2 w hw
  exact ⟨LinearEquiv.ofBijective _ hbij, fun a b => by
    rw [LinearEquiv.ofBijective_apply, wedgeMap_ιMulti]; rfl⟩

end GlobalTheory.AbCoh.Wedge
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePropertyFromFibresStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.wedge_property_from_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Module.Finite R (HO1 s) → Module.Projective R (HO1 s) → Module.Finite R (HO2 s) → Module.Projective R (HO2 s) → StructureSheafH1BaseChange s → StructureSheafH2BaseChange s → (∀ x : HO1 s, cup _ x x = 0) → (∀ (k : Type) [Field k] [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R k))), WedgeO (OAff s')) → WedgeO (OAff s) := by
  first | exact @GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres | exact GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres | (intros; apply GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyNoetherian

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCohRing

theorem rankAtStalk_eq_finrank_residueField {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  rw [Module.rankAtStalk_eq_finrank_tensorProduct]
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) :=
    Module.free_of_flat_of_isLocalRing
  have e := (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal)
    p.asIdeal.ResidueField p.asIdeal.ResidueField M)
  rw [← e.finrank_eq]
  exact (Module.finrank_baseChange (S := Localization.AtPrime p.asIdeal) (R := p.asIdeal.ResidueField)
    (M' := Localization.AtPrime p.asIdeal ⊗[R] M)).symm

theorem exists_grpObj_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) {X' : Scheme.{0}} (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
    (h : IsPullback φ s' A.hom (spMap f)) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  letI : GrpObj ((Over.pullback (spMap f)).obj A) := Functor.grpObjObj
  have hP := isGrpPullback_pullback A (spMap f)
  obtain ⟨hPA, -⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A
    ((Over.pullback (spMap f)).obj A) (pullback.fst A.hom (spMap f)) g hP hA hg
  let e : Over.mk s' ≅ (Over.pullback (spMap f)).obj A := Over.isoMk h.isoPullback (by simp)
  letI gr : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  refine ⟨gr, GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso e ?_ hPA,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg⟩
  haveI : IsMonHom e.symm.hom := inferInstance
  exact isMonHom_inv_of_iso e.symm

end GlobalTheory.AbCohRing

namespace GlobalTheory.AbCohRing

theorem fp_and_bc (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom)) ∧
      (Module.Finite R (HO2 A.hom) ∧ Module.Projective R (HO2 A.hom)) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom := by
  have := hA.proper
  have := hA.smooth
  refine GlobalTheory.T.structure_cohomology_residue_field_fibre R A.left A.hom inferInstance inferInstance (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA) ?_
  intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hφ w
  obtain ⟨_, hA', hg'⟩ := exists_grpObj_of_isPullback (algebraMap R R') A g s' φ hφ hA hg
  exact GlobalTheory.T.abelianSchemeSpecialFibre_cohomology_lift_artinian R' (Over.mk s') g hA' hg' k α hα X₀ s₀ ψ w

theorem rankAtStalk_HO1 (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) [Module.Finite R (HO1 A.hom)]
    [Module.Projective R (HO1 A.hom)] (hb : StructureSheafH1BaseChange A.hom) (p : PrimeSpectrum R) :
    Module.rankAtStalk (HO1 A.hom) p = g := by
  let κ := p.asIdeal.ResidueField
  have hpb := IsPullback.of_hasPullback A.hom (spMap (algebraMap R κ))
  obtain ⟨e, -⟩ := hb κ _ _ _ hpb
  obtain ⟨_, hA', hg'⟩ := exists_grpObj_of_isPullback (algebraMap R κ) A g _ _ hpb hA hg
  have hκ := (GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField κ _ g hA' hg').2.1
  rw [rankAtStalk_eq_finrank_residueField, ← hκ]
  exact e.finrank_eq

theorem oStr_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    FP R (HO1 A.hom) g ∧ WedgeO (OAff A.hom) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom := by
  intro R _ _ A _ g hA hg
  obtain ⟨⟨h1f, h1p⟩, ⟨h2f, h2p⟩, hb1, hb2⟩ := fp_and_bc R A g hA hg
  refine ⟨⟨h1f, h1p, rankAtStalk_HO1 R A g hA hg hb1⟩, ?_, hb1, hb2⟩
  refine GlobalTheory.T.wedge_property_from_fibres R A.left A.hom h1f h1p h2f h2p hb1 hb2 (GlobalTheory.T.cup_self_zero_abelian_h1 R A g hA hg) ?_
  intro k _ _ X' s' φ h
  obtain ⟨_, hA', hg'⟩ := exists_grpObj_of_isPullback (algebraMap R k) A g s' φ h hA hg
  exact (GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField k (Over.mk s') g hA' hg').2.2.1

end GlobalTheory.AbCohRing
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyNoetherianStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_structureSheafCohomology_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FP R (HO1 A.hom) g ∧ WedgeO (OAff A.hom) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom := by
  first | exact @GlobalTheory.AbCohRing.oStr_noetherian | exact GlobalTheory.AbCohRing.oStr_noetherian | (intros; apply GlobalTheory.AbCohRing.oStr_noetherian <;> assumption)
end
end

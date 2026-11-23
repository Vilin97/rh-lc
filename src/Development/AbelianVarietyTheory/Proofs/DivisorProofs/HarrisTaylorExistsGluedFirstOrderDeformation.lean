module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphIsotropicOfDirectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphLieConditionOfDirectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphOrderStableOfDirectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroLiftRealisingKs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandCrystallineLieStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFiltrationStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.RingTheory.DualNumber

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsComplCrystalGluedHodgeGraphFiltration

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem exists_isCompl_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R)
    (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)),
    ∃ M : Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A),
      IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f
  obtain ⟨M₀, hM₀⟩ := Submodule.exists_isCompl (Fil o₀.A)
  exact ⟨_, isCompl_glueFil o₀.A o₀.ab f M₀ hM₀⟩

end GlobalTheory.HTGlue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsComplCrystalGluedHodgeGraphFiltrationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.exists_isCompl_crystalGluedHodgeGraphFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M := by
  first | (exact @GlobalTheory.HTGlue.exists_isCompl_glueFil) | (exact GlobalTheory.HTGlue.exists_isCompl_glueFil) | (intros; apply GlobalTheory.HTGlue.exists_isCompl_glueFil  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandAdmissibleStable

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTDeform


open GlobalTheory.Published.GrothendieckMessing in
theorem liftFil_isCompl_red_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl (liftFil (divided₂ hsq) m.cart) M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ liftFil (divided₂ hsq) m.cart, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ liftFil (divided₂ hsq) m.cart, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ liftFil (divided₂ hsq) m.cart) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _
  have HC := canonical_of_abelianDeRham GlobalTheory.T.abelianScheme_firstDeRham_structure (isDPNilpotent_squareZero hsq) hπ rfl
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  obtain ⟨bij, ⟨M, hM⟩, hAdm⟩ := HC g o₀.A o.A m.φ m.cart o.ab hg
  have bijD := HC.crysToDR_bijective m.cart o.ab hg
  let e := LinearEquiv.ofBijective (crysToDR (divided₂ hsq) m.cart) bijD
  refine ⟨⟨M.comap (crysToDR (divided₂ hsq) m.cart), (Submodule.orderIsoMapComap e).symm.isCompl hM⟩,
    fun y ↦ ?_, fun c d hd ↦ ?_⟩
  · rw [hAdm y]
    constructor
    · rintro ⟨x, hx, ex⟩
      obtain ⟨d, rfl⟩ := bijD.2 x
      exact ⟨d, hx, (corr_crysToDR_iff rfl m.cart bij.2 d y).1 ex⟩
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, hd, (corr_crysToDR_iff rfl m.cart bij.2 d y).2 ed⟩
  · haveI := o₀.act.hom c
    haveI := o.act.hom c
    exact push_mem_liftFil (divided₂ hsq) m.cart m.cart (o₀.act.act c) (o.act.act c) (m.act c).symm hd

end GlobalTheory.HTDeform
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandAdmissibleStableStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_admissible_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl (liftFil (divided₂ hsq) m.cart) M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ liftFil (divided₂ hsq) m.cart, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ liftFil (divided₂ hsq) m.cart, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ liftFil (divided₂ hsq) m.cart) := by
  first | (exact @GlobalTheory.HTDeform.liftFil_isCompl_red_stable) | (exact GlobalTheory.HTDeform.liftFil_isCompl_red_stable) | (intros; apply GlobalTheory.HTDeform.liftFil_isCompl_red_stable  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandIsotropic

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open IsLocalRing GlobalTheory.AbDual

namespace GlobalTheory.HTLiftIso

theorem liftFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) m.cart, ∀ y ∈ liftFil (divided₂ hsq) m.cart, φ x y = 0 := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _ φ hφ x hx y hy
  let κ := GlobalTheory.Cris.divided₂ hsq
  have hκ : GlobalTheory.Cris.IsNilDP κ := GlobalTheory.Cris.isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl o.ab hg o.ab hg m.cart m.cart
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have CD := cupSquare_of_free ADR.1 hAB (smooth_prod hg hg)
  obtain ⟨φd, hφd⟩ := exists_isCorrForm CD o.isLB o.rig₁ o.rig₂
  obtain ⟨φ₀, hφ₀, e₀⟩ := GlobalTheory.Published.AbelianDualCrystal.exists_crystal_pairing κ m.cart m.cart m.sq.1 m.sq.2
    o.isLB o₀.isLB (LBIso.symm m.pol) hφd
  obtain rfl := hφ.unique CS o₀.isLB hφ₀
  rw [e₀]
  obtain ⟨ψ, hψ, eψ⟩ := hφd.isPolForm
  have iso := (ADR.2.2.2.2 C _ _ hAB (smooth_prod hg hg) o.P o.isLB ψ hψ).1
  have hx' : crysToDR κ m.cart x ∈ Fil o.A := hx
  have hy' : crysToDR κ m.cart y ∈ Fil o.A := hy
  have h := iso _ (push_mem_Fil (inl o.A o.A) hx') _ (push_mem_Fil (inr o.A o.A) hy')
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_push _ _ _ (lift_snd _ _)] at h
  simpa [push_id, push_one] using h

end GlobalTheory.HTLiftIso
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandIsotropicStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) m.cart, ∀ y ∈ liftFil (divided₂ hsq) m.cart, φ x y = 0 := by
  first | (exact @GlobalTheory.HTLiftIso.liftFil_isotropic) | (exact GlobalTheory.HTLiftIso.liftFil_isotropic) | (intros; apply GlobalTheory.HTLiftIso.liftFil_isotropic  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem GlobalTheory.HTGlue.isFilLift_coords {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {A' : Over (Sp (DualNumber k))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i)
    {x y : HdR A} (hx : IsFilLift h x y) :
    ∃ e ∈ liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) h,
      ∀ c, e ((GlobalTheory.FODef.constMorV k k A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (y c) := hx

theorem GlobalTheory.HTGlue.exists_obj_of_summand (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hNp : N.Coprime p) (C C₀ : Type) [CommRing C] [IsLocalRing C]
    [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀) (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0)
    (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)) (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A))
    (hEc : ∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M)
    (hEf : ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y)
    (hEs : ∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E)
    (hEi : ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C,
      GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0)
    (hEl : ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
      push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
        push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧
        d - ∑ i, w i ∈ E)
    (s : Sp C ⟶ Sp R) (hs : s = spMap tR) :
    ∃ (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), liftFil (divided₂ hsq) m.cart = E := by
  exact GlobalTheory.T.harrisTaylor_exists_squareZero_lift_of_filtration
    p D R b N hNp C C₀ π hπ hsq tR s (spMap π ≫ spMap tR)
    hs (congrArg (spMap π ≫ ·) hs.symm) o₀ E hEc hEf hEs hEi hEl

theorem GlobalTheory.HTGlue.isFilLiftV_of_eq {k : Type} [Field k] {d : ℕ} {A₀ : Over (Sp k)} [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {A : Over (Sp (TrivSqZeroExt k (Fin d → k)))} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) i)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (hh : liftFil (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) h = GlobalTheory.HTGlue.glueFil A₀ f) {x : HdR A₀}
    (hx : x ∈ Fil A₀) : GlobalTheory.FODef.IsFilLiftV h x (LinearMap.pi fun j => f j x) := by
  obtain ⟨e, he, hc⟩ := GlobalTheory.HTGlue.exists_mem_glueFil A₀ hA f hx
  exact ⟨e, hh ▸ he, hc⟩



theorem GlobalTheory.HTGlue.exists_glue : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ d f hdef
  obtain ⟨tk, ht⟩ : ∃ tk : R →+* k, t = spMap tk :=
    ⟨(Spec.preimage t).hom, (Spec.map_preimage t).symm⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · obtain ⟨φ, hφ⟩ := GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj p D R b N hN hNp k t o₀
    exact GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks p D R b N hN hNp k t o₀ tk ht φ hφ 0 f (fun j => j.elim0)
  have : IsArtinianRing (TrivSqZeroExt k (Fin d → k)) := GlobalTheory.HTGlue.isArtinianRing_tsze k d
  have : Module.Finite k (DualNumber k) :=
    Module.Finite.of_surjective ((Algebra.linearMap k (DualNumber k)).coprod (TrivSqZeroExt.inrHom k k))
      (fun x => ⟨(x.fst, x.snd), TrivSqZeroExt.inl_fst_add_inr_snd_eq x⟩)
  have : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k _
  set tR : R →+* TrivSqZeroExt k (Fin d → k) := (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk
  choose o' m' hm' using hdef
  have hsε : spMap (algebraMap k (DualNumber k)) ≫ t =
      spMap ((algebraMap k (DualNumber k)).comp tk) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have hs₀ : t =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ((algebraMap k (TrivSqZeroExt k k)).comp tk) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    congr 1
  have hsurε : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hAdmissible := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_admissible_stable
    p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom
    hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk)
    (spMap (algebraMap k (DualNumber k)) ≫ t) t o₀ (o' j) (m' j) hsε hs₀
  have hDirectionIso := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_isotropic
    p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom
    hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk)
    (spMap (algebraMap k (DualNumber k)) ≫ t) t o₀ (o' j) (m' j) hsε hs₀
  have hDirectionLie := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_crystalline_lie
    p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom
    hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk)
    (spMap (algebraMap k (DualNumber k)) ≫ t) t o₀ (o' j) (m' j) hsε hs₀
  have hmem (j : Fin d) (x : HdR o₀.A) (hx : x ∈ Fil o₀.A) :=
    GlobalTheory.HTGlue.isFilLift_coords (m' j).cart (hm' j x hx)
  have hCompl (j : Fin d) := (hAdmissible j).1
  have hRed (j : Fin d) := (hAdmissible j).2.1
  have hStable (j : Fin d) := (hAdmissible j).2.2
  have hGluedCompl := GlobalTheory.T.exists_isCompl_crystalGluedHodgeGraphFiltration p D R b N k tk t o₀ ht d f
  have hGluedRed := GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFiltration p D R b N k tk t o₀ ht d f
  -- Match the filtration hypotheses without unfolding the crystalline modules.
  have hGluedStable := GlobalTheory.T.crystalGluedHodgeGraph_order_stable_of_directions p D R b N k tk t o₀ ht d f
    (fun j => liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) (m' j).cart)
    (by with_reducible exact hCompl) (by with_reducible exact hRed)
    (by with_reducible exact hmem) (by with_reducible exact hStable)
  have hGluedIso := GlobalTheory.T.crystalGluedHodgeGraph_isotropic_of_directions p D R b N k tk t o₀ ht d f
    (fun j => liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) (m' j).cart)
    (by with_reducible exact hCompl) (by with_reducible exact hRed)
    (by with_reducible exact hmem) (by with_reducible exact hStable) (by with_reducible exact hDirectionIso)
  have hGluedLie := GlobalTheory.T.crystalGluedHodgeGraph_lie_condition_of_directions p D R b N k tk t o₀ ht d hd f
    (fun j => liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) (m' j).cart)
    (by with_reducible exact hCompl) (by with_reducible exact hRed)
    (by with_reducible exact hmem) (by with_reducible exact hStable) (by with_reducible exact hDirectionLie)
  have hsurC : Function.Surjective (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hst : spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t = spMap tR := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have hs₀C : t = spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫
      (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) := by
    rw [hst, ht, ← GlobalTheory.Cris.spMap_comp]
    congr 1
  have hObj := GlobalTheory.T.harrisTaylor_exists_squareZero_lift_of_filtration p D R b N hNp
    (TrivSqZeroExt k (Fin d → k)) k (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom
    hsurC (GlobalTheory.FODef.sqZero k (Fin d → k)) tR
    (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) t hst hs₀C o₀
    (GlobalTheory.HTGlue.glueFil o₀.A f)
    (by with_reducible exact hGluedCompl) (by with_reducible exact hGluedRed) (by with_reducible exact hGluedStable)
    (by with_reducible exact hGluedIso) (by with_reducible exact hGluedLie)
  obtain ⟨o, m, hm⟩ := hObj
  exact ⟨o, m, fun x hx => GlobalTheory.HTGlue.isFilLiftV_of_eq o₀.ab m.cart f hm hx⟩
end
end

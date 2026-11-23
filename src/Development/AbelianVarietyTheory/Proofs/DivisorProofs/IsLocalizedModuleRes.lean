module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldBasisToroidalModelSnc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Mathlib.RingTheory.TotallySplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldBasisToroidalModelSncStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_logVectorField_basis_toroidalModel_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (x : Y.X), x ∈ U.1 → ∃ (f : Γ(Y.X, U.1)) (W : Y.X.affineOpens) (hW : W.1 ≤ U.1) (m : ℕ) (t : Fin m → Γ(Y.X, W.1)) (b : Module.Basis (Fin Dw.dim) Γ(Y.X, W.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) W)), x ∈ W.1 ∧ W.1 = Y.X.basicOpen f ∧ (∀ g ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W, g ∈ Ideal.span {∏ i, t i}) ∧ ∏ i, t i ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W ∧ ∀ (i : Fin m) (k : Fin Dw.dim), ((b k).1 : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (t i) = if (k : ℕ) = i then t i else 0 := by
  first | exact @GlobalTheory.LogBasis.exists_logDer_basis | exact GlobalTheory.LogBasis.exists_logDer_basis | (intros; apply GlobalTheory.LogBasis.exists_logDer_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAwStatement

section

@[expose] public section

open GlobalTheory.LogDerProj

theorem _root_.GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R), ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_res | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_res | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_res <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEqStatement

section

@[expose] public section

open GlobalTheory.LogDerProj

theorem _root_.GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (D₁ D₂ : logSub φ J), res (S := S) f φ J D₁ = res (S := S) f φ J D₂ → ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocallyFiniteFreeLocalizations

section

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFreeProj

theorem finite_projective_of_locally_free : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M], (∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ) → Module.Finite R M ∧ Module.Projective R M := by
  intro R _ M _ _ h
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iFree ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iFree
  haveI := hϕ
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.LocFreeProj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizedModuleRes

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LogDerProj

namespace GlobalTheory.LogDerProj

theorem isLocalizedModule_res : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ J : Ideal R, IsLocalizedModule (Submonoid.powers f) (res (S := S) f φ J) := by
  intro k R S _ _ _ _ f _ φ hφ J
  refine IsLocalizedModule.mk (fun x => ?_) (GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway f φ hφ J) (GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq f φ hφ J _ _)
  have hu : IsUnit (algebraMap R S x) := IsLocalization.map_units S x
  rw [Module.End.isUnit_iff]
  constructor
  · intro n n' h
    have h' : algebraMap R S x • n.1 = algebraMap R S x • n'.1 := by
      simpa [algebraMap_smul] using congrArg Subtype.val h
    exact Subtype.ext ((hu.smul_left_cancel).1 h')
  · intro n
    refine ⟨⟨((hu.unit⁻¹ : Sˣ) : S) • n.1, (show _ ∈ logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S)) from
      Submodule.smul_mem _ _ n.2)⟩, Subtype.ext ?_⟩
    change (x : R) • (((hu.unit⁻¹ : Sˣ) : S) • n.1) = n.1
    rw [← algebraMap_smul S (x : R), smul_smul, IsUnit.mul_val_inv, one_smul]

theorem finrank_fibre : ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (f : R) (d : ℕ) (ϕ : M →ₗ[R] (Fin d → Localization.Away f)), IsLocalizedModule (Submonoid.powers f) ϕ → ∀ m : Ideal R, m.IsMaximal → f ∉ m → Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = d := by
  intro R M _ _ _ f d ϕ hϕ m hm hf
  letI := Ideal.Quotient.field m
  have hu : IsUnit (algebraMap R (R ⧸ m) f) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf
  letI : Algebra (Localization.Away f) (R ⧸ m) := (IsLocalization.Away.lift f hu).toAlgebra
  haveI : IsScalarTower R (Localization.Away f) (R ⧸ m) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hbc : IsBaseChange (Localization.Away f) ϕ := IsLocalizedModule.isBaseChange (Submonoid.powers f) _ ϕ
  let e1 := hbc.equiv
  let e2 := TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away f) (R ⧸ m) (R ⧸ m) M
  let e3 := LinearEquiv.baseChange (Localization.Away f) (R ⧸ m) _ _ e1
  rw [← e2.finrank_eq, e3.finrank_eq, Module.finrank_eq_card_basis
    (Algebra.TensorProduct.basis (R ⧸ m) (Pi.basisFun (Localization.Away f) (Fin d))), Fintype.card_fin]

end GlobalTheory.LogDerProj



theorem GlobalTheory.LogDerProj.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ U : Y.X.affineOpens, Module.Finite Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) ∧ Module.Projective Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U
  haveI : SmoothOfRelativeDimension Dw.dim Y.s := smooth_gen_iff.1 hsm
  haveI : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  set I := Scheme.IdealSheafData.vanishingIdeal (interior Y).compl with hI
  let φ : c.F →+* Γ(Y.X, U.1) := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.s U.1
  have hφ : φ.FiniteType := by
    have h1 : (Y.s.appLE ⊤ U.1 (by simp)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType Y.s inferInstance ⟨⊤, isAffineOpen_top _⟩ U _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.surjective)
  have hM : logDer Y.s I U = GlobalTheory.LogDerProj.logSub φ (I.ideal U) := rfl
  have loc : ∀ q : PrimeSpectrum Γ(Y.X, U.1), ∃ r ∉ q.asIdeal,
      ∃ ϕ : GlobalTheory.LogDerProj.logSub φ (I.ideal U) →ₗ[Γ(Y.X, U.1)] (Fin Dw.dim → Localization.Away r),
        IsLocalizedModule (Submonoid.powers r) ϕ := by
    intro q
    have hU : IsAffineOpen U.1 := U.2
    have hxU : hU.fromSpec q ∈ U.1 := by
      change _ ∈ (U.1 : Set Y.X)
      rw [← hU.range_fromSpec]
      exact ⟨q, rfl⟩
    have key := GlobalTheory.T.exists_logVectorField_basis_toroidalModel_snc E H Dw l Xo c Y h1 hsm hsnc U (hU.fromSpec q) hxU
    obtain ⟨f, W, hW, m, t, b, hxW, hWf, -⟩ := key
    have hq : f ∉ q.asIdeal := by
      have : q ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen f := by rw [← hWf]; exact hxW
      rw [hU.fromSpec_preimage_basicOpen] at this
      exact this
    letI : Algebra Γ(Y.X, U.1) Γ(Y.X, W.1) := (Y.X.presheaf.map (homOfLE hW).op).hom.toAlgebra
    have hloc : ∀ (V : Y.X.Opens) (hV : V ≤ U.1), V = Y.X.basicOpen f →
        letI := (Y.X.presheaf.map (homOfLE hV).op).hom.toAlgebra; IsLocalization.Away f Γ(Y.X, V) := by
      rintro V hV rfl
      exact U.2.isLocalization_basicOpen f
    haveI : IsLocalization.Away f Γ(Y.X, W.1) := hloc W.1 hW hWf
    have hc : ∀ a, algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1) (φ a) = constFn Y.s W.1 a :=
      fun a => congr(($(Scheme.Hom.appLE_map Y.s (U := ⊤) (V := U.1) (fun _ _ => trivial) (homOfLE hW).op)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a))
    have hid : (I.ideal U).map (algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1)) = I.ideal W := I.map_ideal (U := W) (V := U) hW
    have hN : logDer Y.s I W = GlobalTheory.LogDerProj.logSub
        ((algebraMap Γ(Y.X, U.1) Γ(Y.X, W.1)).comp φ) ((I.ideal U).map (algebraMap _ _)) := by
      ext D
      rw [GlobalTheory.LogDerProj.mem_logSub, hid]
      simp only [RingHom.comp_apply, hc]
      rfl
    let b' := b.map (LinearEquiv.ofEq _ _ hN)
    let e := (b'.equivFun.restrictScalars Γ(Y.X, U.1)).trans (LinearEquiv.piCongrRight fun _ =>
      (IsLocalization.algEquiv (Submonoid.powers f) Γ(Y.X, W.1) (Localization.Away f)).toLinearEquiv)
    haveI := GlobalTheory.LogDerProj.isLocalizedModule_res (S := Γ(Y.X, W.1)) f φ hφ (I.ideal U)
    exact ⟨f, hq, e.toLinearMap ∘ₗ GlobalTheory.LogDerProj.res (S := Γ(Y.X, W.1)) f φ (I.ideal U),
      IsLocalizedModule.of_linearEquiv (Submonoid.powers f) (GlobalTheory.LogDerProj.res (S := Γ(Y.X, W.1)) f φ (I.ideal U)) e⟩
  rw [hM]
  obtain ⟨hfin, hproj⟩ := GlobalTheory.LocFreeProj.finite_projective_of_locally_free _ _ fun q => by
    obtain ⟨r, hr, ϕ, hϕ⟩ := loc q
    exact ⟨r, hr, Fin Dw.dim → Localization.Away r, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ϕ, hϕ⟩
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  obtain ⟨r, hr, ϕ, hϕ⟩ := loc ⟨m, hm.isPrime⟩
  exact GlobalTheory.LogDerProj.finrank_fibre r Dw.dim ϕ hϕ m hm hr
end
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtensionCompletedEtaleChart
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkIdealVanishingIdealPreimageIsoStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendStalkOfIso

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDer

theorem derivation_extend_stalk_of_iso : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (U : X.affineOpens) (d : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ∃ δ : Derivation ℤ (X'.presheaf.stalk x) (X'.presheaf.stalk x), ∀ r, δ ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom r)) = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom (d r)) := by
  intro X X' f _ U d x hx
  have hU' : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  let φ : Γ(X, U.1) ≃+* Γ(X', f ⁻¹ᵁ U.1) := (asIso (f.app U.1)).commRingCatIsoToRingEquiv
  letI : Algebra Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x) :=
    X'.presheaf.algebra_section_stalk (⟨x, hx⟩ : f ⁻¹ᵁ U.1)
  haveI := hU'.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ a, algebraMap Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x) a =
      (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom a := fun a => rfl
  let g : Γ(X', f ⁻¹ᵁ U.1) →+ X'.presheaf.stalk x :=
    (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.toAddMonoidHom.comp
      (φ.toRingHom.toAddMonoidHom.comp (d.toLinearMap.toAddMonoidHom.comp φ.symm.toRingHom.toAddMonoidHom))
  have hg : ∀ a, g a = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom (φ (d (φ.symm a))) := fun a => rfl
  obtain ⟨D', hD'⟩ := derivation_extend_localization_atPrime ℤ Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x)
    (hU'.primeIdealOf ⟨x, hx⟩).asIdeal
    (intDerivationOfLeibniz g (fun a b => by
      simp only [hg, map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), Algebra.smul_def, halg,
        RingEquiv.apply_symm_apply]))
  refine ⟨D', fun r => ?_⟩
  have h1 := hD' (φ r)
  rw [halg] at h1
  refine h1.trans ?_
  show g (φ r) = _
  rw [hg, RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.StalkDer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendStalkOfIsoStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_derivation_stalk_extend_of_app : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (U : X.affineOpens) (d : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ∃ δ : Derivation ℤ (X'.presheaf.stalk x) (X'.presheaf.stalk x), ∀ r, δ ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom r)) = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom (d r)) := by
  first | exact @GlobalTheory.StalkDer.derivation_extend_stalk_of_iso | exact GlobalTheory.StalkDer.derivation_extend_stalk_of_iso | (intros; apply GlobalTheory.StalkDer.derivation_extend_stalk_of_iso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtensionCompletedEtaleChartStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_derivation_extension_completedEtaleChart : ∀ (A : Type) [CommRing A] [IsLocalRing A] (k : Type) [Field k] [CharZero k] (m d : ℕ) (ψ : A →+* ChartRing k m d), IsEtaleCompletion ψ → ∀ δ : Derivation ℤ A A, ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), ∀ a, D' (ψ a) = ψ (δ a) := by
  first | exact @GlobalTheory.ChartDerivation.main | exact GlobalTheory.ChartDerivation.main | (intros; apply GlobalTheory.ChartDerivation.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartDerivationBoundaryParamMemSpan

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDerBd

theorem X_dvd_of_X_mul {σ K : Type} [Field K] {s t : σ} (hst : t ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ MvPowerSeries.X t * g) : MvPowerSeries.X s ∣ g := by
  classical
  rw [MvPowerSeries.X_dvd_iff] at h ⊢
  intro n hn
  have h1 := h (n + Finsupp.single t 1) (by simp [Finsupp.single_apply, hst, hn])
  rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul] at h1
  simpa using h1

theorem X_dvd_of_prod_mul {σ K : Type} [Field K] {Idx : Type} (f : Idx → σ) {s : σ}
    (S : Finset Idx) (hS : ∀ j ∈ S, f j ≠ s) {g : MvPowerSeries σ K}
    (h : MvPowerSeries.X s ∣ (∏ j ∈ S, MvPowerSeries.X (f j)) * g) : MvPowerSeries.X s ∣ g := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, _root_.mul_assoc] at h
    exact ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
      (X_dvd_of_X_mul (hS a (Finset.mem_insert_self a S)) h)

theorem deriv_bdParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  classical
  intro A _ k _ m d ψ δ D' I hI hD hJ i

  have hpres : ∀ x ∈ I.map ψ, D' x ∈ I.map ψ := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD]
      exact Ideal.mem_map_of_mem ψ (hI a ha)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
    | smul r x hxm hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ r hx)
        (Ideal.mul_mem_right _ _ (Ideal.span_le.2 (fun y hy => Ideal.subset_span hy) hxm))
  set t := bdParam k m d with ht
  have hP : t i * ∏ j ∈ Finset.univ.erase i, t j = ∏ j, t j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hmem : D' (∏ j, t j) ∈ Ideal.span {∏ j, t j} := by
    rw [← hJ]; apply hpres; rw [hJ]; exact Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton] at hmem ⊢
  rw [← hP, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hmem
  have h1 : t i ∣ t i * D' (∏ j ∈ Finset.univ.erase i, t j) + (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_mul_right (t i) _).trans hmem
  have h2 : t i ∣ (∏ j ∈ Finset.univ.erase i, t j) * D' (t i) :=
    (dvd_add_right (dvd_mul_right _ _)).1 h1
  exact X_dvd_of_prod_mul (fun j : Fin m => (Sum.inl j : Fin m ⊕ Fin d)) (Finset.univ.erase i)
    (fun j hj h => (Finset.ne_of_mem_erase hj) (Sum.inl_injective h)) h2

end GlobalTheory.ChartDerBd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartDerivationBoundaryParamMemSpanStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.toricChart_derivation_boundaryParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  first | exact @GlobalTheory.ChartDerBd.deriv_bdParam_mem_span | exact GlobalTheory.ChartDerBd.deriv_bdParam_mem_span | (intros; apply GlobalTheory.ChartDerBd.deriv_bdParam_mem_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRing

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDer

theorem logDer_extend_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} → ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) r) = ((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) (D.1 r)) ∧ ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  intro E _ _ _ H Dw l Xo c Y U D k _ m d ξ hx hE hI
  have hiso : IsIso (genι Y) := isIso_fst Y
  set x := ξ (closedPoint _) with hxdef
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_derivation_stalk_extend_of_app _ _ (genι Y) U D.1 x hx
  set g := ((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) x hx).hom.comp ((genι Y).app U.1).hom with hg
  have hZ : ((genBd Y : TopologicalSpace.Closeds (gen Y)) : Set (gen Y)) = (genι Y) ⁻¹' ((interior Y).compl : Set Y.X) := by
    ext z
    simp only [TopologicalSpace.Opens.coe_compl, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
    rw [mem_genBd]
    unfold GlobalTheory.LogKS.interior Model.j
    have hc : ∀ w, (Y.jQ ≫ pullback.fst Y.s (spMap (RingHom.id c.F))) w = genι Y (Y.jQ w) := fun w => rfl
    simp only [Scheme.Hom.coe_opensRange, Set.mem_range, hc]
    constructor
    · rintro h ⟨w, hw⟩
      exact h ⟨w, (genι Y).isOpenEmbedding.injective hw⟩
    · rintro h ⟨w, hw⟩
      exact h ⟨w, by rw [← hw]; rfl⟩
  have hJ := GlobalTheory.T.stalkIdeal_vanishingIdeal_preimage_iso _ _ (genι Y) _ (genBd Y) hZ U x hx
  have hstab : ∀ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g,
      δ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      have := hδ r
      simp only [hg, RingHom.comp_apply] at this ⊢
      rw [this]
      exact Ideal.mem_map_of_mem _ (D.2.2 r hr)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Ideal.add_mem _ hy hz
    | smul c y hy' hy =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hy')
  have hC : CharZero (ChartRing k m d) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hk : CharZero k := (RingHom.charZero_iff (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))).2 hC
  obtain ⟨D', hD'⟩ := GlobalTheory.T.exists_derivation_extension_completedEtaleChart _ k m d (Scheme.stalkClosedPointTo ξ).hom hE δ
  refine ⟨D', fun r => ?_, GlobalTheory.T.toricChart_derivation_boundaryParam_mem_span _ k m d _ δ D' _ hstab hD' (by rw [← hJ]; exact hI)⟩
  simp only [RingHom.comp_apply]
  rw [hD']
  exact congrArg _ (hδ r)

end GlobalTheory.ChartDer
end
end

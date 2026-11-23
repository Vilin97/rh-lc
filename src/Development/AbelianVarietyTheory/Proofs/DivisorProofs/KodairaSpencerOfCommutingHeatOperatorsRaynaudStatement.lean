module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrimitiveScaling
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingHeatOperatorsActOnValuesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalPointOriginSmoothCommGroupSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerAbelianLocusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupPointSameDerivationsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolUniquePrincipalPolarisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsKodairaSpencerFormalPointValuesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRaynaudExtensionNoetherianLocalStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasis
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerAffineChartOfBasicOpen

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

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.KSChartRes

theorem isUnit_of_comap_mem {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) (s : A)
    (h : ∀ x : PrimeSpectrum S, PrimeSpectrum.comap φ x ∈ PrimeSpectrum.basicOpen s) : IsUnit (φ s) := by
  by_contra hn
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hn)
  exact h ⟨m, hm.isPrime⟩ (hsm (Ideal.mem_span_singleton_self _))

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem isKS_top_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t m tt n v' D DV Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩

  set s := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i) with hs
  set Wa := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) s with hWa
  have hWV : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ Wa.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  have hle : Wa.1 ≤ ⊤ := le_top
  refine ⟨J, Wc, j, d, ?_, hj, hfld, fun i h r => ?_, fun i i' O hO f S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [hsup, top_inf_eq]
    exact congrArg _ (inf_idem _)
  · have e : ∀ x, (t.G.hom.appLE ⊤ (Wc i) h).hom x =
        (t.G.hom.appLE Wa.1 (Wc i) (hWV i)).hom (((Sp R).presheaf.map (homOfLE hle).op).hom x) := fun x =>
      (congrArg (fun k => k.hom x) (t.G.hom.map_appLE (hWV i) (homOfLE hle).op)).symm
    have hr : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
      Iso.hom_inv_id_apply _ _
    rw [e, e, hcomp i (hWV i)]
    have := hD ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)
    rw [hr] at this
    exact congrArg _ this
  · have hOW : O ≤ t.G.hom ⁻¹ᵁ (Wa.1 ⊓ (Sp R).basicOpen s) :=
      hO.trans (inf_le_left.trans ((le_iSup Wc i).trans hsup.le))
    have hu : IsUnit (φ s) := by
      refine isUnit_of_comap_mem φ s fun x => ?_
      have hx : g₀ x ∈ O := hO' (show x ∈ (⊤ : (Sp S).Opens) from trivial)
      have hV : t.G.hom (g₀ x) ∈ (Sp R).basicOpen s := (hOW hx).2
      have e1 : t.G.hom (g₀ x) = (g₀ ≫ t.G.hom) x := rfl
      rw [e1, hg₀] at hV
      have h2 : (spMap φ) x ∈ (GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ (Sp R).basicOpen s := hV
      change (spMap φ) x ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen s at h2
      rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen s] at h2
      exact h2
    letI : Algebra Γ(Sp R, ⊤) Γ(Sp R, Wa.1) := ((Sp R).presheaf.map (homOfLE hle).op).hom.toAlgebra
    have hl : IsLocalization.Away s Γ(Sp R, Wa.1) :=
      (isAffineOpen_top (Sp R)).isLocalization_of_eq_basicOpen s (homOfLE hle) rfl
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(Sp R, Wa.1) →+* S, ψ.comp ((Sp R).presheaf.map (homOfLE hle).op).hom = φ :=
      ⟨IsLocalization.Away.lift s hu, IsLocalization.lift_comp _⟩
    subst hψ
    have hres : spMap ((Sp R).presheaf.map (homOfLE hle).op).hom ≫
        GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) = GlobalTheory.LogKS.chart Wa :=
      (isAffineOpen_top (Sp R)).map_fromSpec Wa.2 (homOfLE hle).op
    have := htest i i' O hO f S ψ g₀ w ?_ hO' ?_
    · exact this
    · rw [hg₀, ← hres, ← Category.assoc, spMap_comp']
    · intro a
      obtain ⟨g', v'', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v'', h₁, ?_, h₃⟩
      rw [h₂]
      dsimp only
      rw [← Category.assoc, ← Category.assoc, spMap_comp']
      erw [spMap_comp']
      erw [dualMap_comp']

end GlobalTheory.KSChartRes
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerAffineChartOfBasicOpenStatement

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

theorem _root_.GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  first | exact @GlobalTheory.KSChartRes.isKS_top_of_basicOpen | exact GlobalTheory.KSChartRes.isKS_top_of_basicOpen | (intros; apply GlobalTheory.KSChartRes.isKS_top_of_basicOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUniformisedGroupOfRaynaudExtension

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

namespace GlobalTheory.TanRayBasis

theorem vBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ⇑b = v' := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  obtain ⟨b, hb⟩ := GlobalTheory.TanRay.tanBasis_of_isPointOf E H R t P Y n vH v' hv
  exact ⟨b, funext hb⟩

end GlobalTheory.TanRayBasis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUniformisedGroupOfRaynaudExtensionStatement

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

theorem _root_.GlobalTheory.T.tangentBasis_uniformisedGroup_of_raynaudExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ⇑b = v' := by
  first | exact @GlobalTheory.TanRayBasis.vBasis_of_isPointOf | exact GlobalTheory.TanRayBasis.vBasis_of_isPointOf | (intros; apply GlobalTheory.TanRayBasis.vBasis_of_isPointOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaud

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

namespace GlobalTheory.KBracket

theorem exists_der_ext {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ δS : Derivation ℤ S S, ∀ a, δS (algebraMap A S a) = algebraMap A S (δ a) := by
  let h : A →+* DualNumber S :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A S a) + TrivSqZeroExt.inr (algebraMap A S (δ a))
      map_one' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz, Algebra.smul_def, mul_comm, add_comm, -DualNumber.inr_eq_smul_eps]
      map_zero' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_add' := fun a b => by ext <;> simp [add_add_add_comm, -DualNumber.inr_eq_smul_eps] }
  have hu : ∀ m : M, IsUnit (h m) := fun m => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [h] using IsLocalization.map_units S m)
  let L : S →+* DualNumber S := IsLocalization.lift hu
  have hfst : ∀ x, (L x).fst = x := by
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp L = RingHom.id S := by
      refine IsLocalization.ringHom_ext M (RingHom.ext fun a => ?_)
      simp [L, h, -DualNumber.inr_eq_smul_eps]
    exact fun x => congr($this x)
  let δS : Derivation ℤ S S := Derivation.mk'
    ((show S →+ S from
      { toFun := fun x => (L x).snd, map_zero' := by simp, map_add' := fun x y => by simp }).toIntLinearMap)
    (fun x y => by
      show (L (x * y)).snd = x • (L y).snd + y • (L x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
      simp [mul_comm])
  refine ⟨δS, fun a => ?_⟩
  show (L (algebraMap A S a)).snd = _
  simp [L, h, Algebra.smul_def, -DualNumber.inr_eq_smul_eps]

theorem exists_der_fun {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ f : S →+ S, (∀ x y, f (x * y) = x * f y + y * f x) ∧
      ∀ a, f (algebraMap A S a) = algebraMap A S (δ a) := by
  obtain ⟨δS, hδS⟩ := exists_der_ext M δ (S := S)
  exact ⟨δS.toLinearMap.toAddMonoidHom, fun x y => by simp [Derivation.leibniz, smul_eq_mul], hδS⟩

theorem exists_der_frac (Ω : Type) [CommRing Ω] [IsDomain Ω] (δ : Derivation ℤ Ω Ω) :
    ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω) := by
  obtain ⟨f, hf1, hf2⟩ := exists_der_fun (nonZeroDivisors Ω) δ (S := FractionRing Ω)
  have hf0 : f 1 = 0 := by
    have h11 := hf1 1 1
    rw [_root_.mul_one, _root_.one_mul] at h11
    linear_combination -h11
  have hfc : ∀ (c : ℤ) (y : FractionRing Ω), f ((c : FractionRing Ω) * y) = (c : FractionRing Ω) * f y := by
    intro c y
    have h2 : f (c : FractionRing Ω) = 0 := by
      rw [← zsmul_one, map_zsmul, hf0]
      simp
    rw [hf1, h2]
    simp
  refine ⟨{ toFun := f
            map_add' := f.map_add
            map_smul' := (fun c y => ?_)
            map_one_eq_zero' := hf0
            leibniz' := (fun x y => ?_) }, hf2⟩
  · simp only [RingHom.id_apply]
    rw [Algebra.smul_def, eq_intCast, zsmul_eq_mul]
    exact hfc c y
  · exact hf1 x y

theorem isKS_of_heat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix h.Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
  letI := H.starRing
  have hsm : Smooth Y.H.hom := GlobalTheory.RayTan.smooth_H R _ _ _ Y
  have hint : IsIntegral Y.H.left := GlobalTheory.T.isIntegral_raynaudExtension_noetherian_local R _ _ _ Y
  obtain ⟨i0, hi0⟩ : ∃ i0, ⊤ ≤ (η[Y.H]).left ⁻¹ᵁ h.W i0 := by
    have hm : (η[Y.H]).left (IsLocalRing.closedPoint R) ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i0, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨i0, (ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem ((η[Y.H]).left ⁻¹ᵁ h.W i0) hi).ge⟩
  obtain ⟨Ω, _, _, _, φ, x, δ, dΩ, hΩc, hx, hxW, hdΩ, hδφ, hδ, hd, hinj⟩ :=
    GlobalTheory.T.exists_formalPoint_origin_smoothCommGroupScheme R Y.H hsm hint n vH dd hdd ⇑D (h.W i0) (h.d i0) (h.lift i0) hi0
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : valR x ⊤ (Y.H.hom.appTop.hom (e.inv.hom r)) = φ r := by
      refine (GlobalTheory.ZH.EvCrd.valR_comp x Y.H.hom ⊤ (by simp) _).trans ?_
      rw [hx]
      exact GlobalTheory.ZH.EvCrd.valR_fn φ r
    have h2 := GlobalTheory.PrimScale.valR_const (η[Y.H]).left Y.H.hom (Over.w η[Y.H]) r
    have h3 := hinj ⊤ _ (by simp) (h1.trans hr)
    rw [h3] at h2
    rw [← h2]
    simp [valR]

  obtain ⟨x', hx', dd', hdd', hδ', hinj', hpt⟩ :=
    GlobalTheory.T.exists_uniformisedGroup_point_sameDerivations E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' Ω φ x δ hΩc hφ hx hδφ hδ
  obtain ⟨g, hg⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := Ω) t.PP.L t.PP.isLB (K := PUnit)
    (fun _ => x' ≫ 𝟙 t.G.left) (fun _ => 1)
  have hex : ∀ a, ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ a ω) :=
    fun a => exists_der_frac Ω (δ a)
  choose δL hδL using hex
  obtain ⟨dt, u', p, p', hdt, hact⟩ := GlobalTheory.T.commuting_heatOperators_act_on_values E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
    i0 Ω φ x x' δ hΩc hx hx' hδφ hδ hpt dΩ hxW hd g hg δL hδL
  obtain ⟨b, rfl⟩ := GlobalTheory.T.tangentBasis_uniformisedGroup_of_raynaudExtension E H R t P Y n vH v' hv'
  let D₀ : Derivation ℤ Γ(Sp R, ⊤) Γ(Sp R, ⊤) := Derivation.mk'
    ((e.inv.hom.toAddMonoidHom.comp ((D : R →ₗ[ℤ] R).toAddMonoidHom.comp e.hom.hom.toAddMonoidHom)).toIntLinearMap)
    (fun a a' => by
      simp [Derivation.leibniz, smul_eq_mul])
  haveI := (isAffineOpen_top (Sp R)).isLocalization_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  obtain ⟨DV, hDV⟩ := exists_der_ext (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) D₀ (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))))
  have hDV' : ∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (D r)) := fun r => by
    show DV (algebraMap _ _ (e.inv.hom r)) = algebraMap _ _ (e.inv.hom (D r))
    rw [hDV]
    congr 1
    simp [D₀]

  obtain ⟨Θ₁, hsym, hKS⟩ := GlobalTheory.T.exists_symmetric_kodairaSpencer_abelianLocus E H R t P m tt gam hmon htt hab n b DV
  obtain ⟨iota, dt₂, u₂, p₂, p₂', hiota, hdt₂, hact₂⟩ := GlobalTheory.T.heatOperators_kodairaSpencer_formal_point_values E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd'
    hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL Θ₁ DV hDV' hKS
  have heq := GlobalTheory.T.heatOperator_symbol_unique_principalPolarisation E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd' hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL
    (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) (iota.mapMatrix Θ₁) dt dt₂ u' u₂ p p' p₂ p₂'
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, h.symm])
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, hsym])
    (fun r => (hdt r).trans (hdt₂ r).symm) hact hact₂
  have hi : Function.Injective iota := by
    have key : ∀ y : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))), iota y = 0 → y = 0 := by
      intro y hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) y
      dsimp only at hy ⊢
      have h1 : iota (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) a) = 0 := by
        rw [← IsLocalization.mk'_spec (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) a s]
        erw [map_mul, hy, zero_mul]
      have h2 : (algebraMap Γ(Sp R, ⊤) _ a : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (e.hom.hom a)) := by
        rw [Iso.hom_inv_id_apply]
        rfl
      rw [h2, hiota] at h1
      have h3 : φ (e.hom.hom a) = 0 := IsFractionRing.injective Ω (FractionRing Ω) (by rw [h1, map_zero])
      have h4 : e.hom.hom a = 0 := hφ (by rw [h3, map_zero])
      have h5 : a = 0 := by simpa using congrArg e.inv.hom h4
      rw [h5, IsLocalization.mk'_zero]
    exact (injective_iff_map_eq_zero iota).2 key
  have hΘ : Θ₁ = (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp e.inv.hom).mapMatrix h.Θ := by
    ext a a'
    apply hi
    have := congrFun (congrFun heq a) a'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply] at this ⊢
    rw [← this, hiota]
  rw [hΘ] at hKS
  exact GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen E H R t m tt n ⇑b D DV h.Θ hDV' hKS

end GlobalTheory.KBracket
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaudStatement

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

theorem _root_.GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix h.Θ) := by
  first | exact @GlobalTheory.KBracket.isKS_of_heat | exact GlobalTheory.KBracket.isKS_of_heat | (intros; apply GlobalTheory.KBracket.isKS_of_heat <;> assumption)
end
end

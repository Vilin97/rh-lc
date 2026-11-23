module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerInteriorAffineOpen
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRegularNearRigidBoundaryPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapComp

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

namespace GlobalTheory.LogKSUp

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem chart_res' {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE h).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  U.2.map_fromSpec W.2 (homOfLE h).op

theorem exists_factor {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (hr : ∀ z, (spMap φ ≫ GlobalTheory.LogKS.chart U) z ∈ W.1) :
    ∃ φ' : Γ(X, W.1) →+* S, φ = φ'.comp (X.presheaf.map (homOfLE h).op).hom := by
  have hr' : Set.range (spMap φ ≫ GlobalTheory.LogKS.chart U) ⊆ Set.range (GlobalTheory.LogKS.chart W) := by
    show _ ⊆ Set.range (IsAffineOpen.fromSpec W.2)
    rw [W.2.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hr z
  have : IsOpenImmersion (GlobalTheory.LogKS.chart W) := W.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (GlobalTheory.LogKS.chart U) := U.2.isOpenImmersion_fromSpec
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Sp S ⟶ Sp Γ(X, W.1), ψ ≫ GlobalTheory.LogKS.chart W = spMap φ ≫ GlobalTheory.LogKS.chart U :=
    ⟨IsOpenImmersion.lift (GlobalTheory.LogKS.chart W) _ hr', IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨(Spec.preimage ψ).hom, ?_⟩
  have hfac : spMap (Spec.preimage ψ).hom ≫ GlobalTheory.LogKS.chart W = spMap φ ≫ GlobalTheory.LogKS.chart U := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    exact hψ
  rw [← chart_res' U W h, ← Category.assoc, spMap_comp''] at hfac
  have h2 := Spec.map_inj.1 ((cancel_mono (GlobalTheory.LogKS.chart U)).1 hfac)
  simpa using (congrArg CommRingCat.Hom.hom h2).symm

end GlobalTheory.LogKSUp

namespace GlobalTheory.LogKSUp

theorem isKS_of_inf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U W : X.affineOpens) (hW : W.1 = U.1 ⊓ V) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (DW : Γ(X, W.1) → Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ r, DW ((X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D r)) → IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW ((X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom.mapMatrix Θ) → IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U W hW n v D DW Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  have hWW : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ W.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, Wc, j, d, ?_, hj, hfld, fun i h r => ?_, fun i i' O hO f S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [hsup, hW, inf_assoc, inf_idem]
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE U.1 (Wc i) h).hom r =
        (t.G.hom.appLE W.1 (Wc i) (hWW i)).hom ((X.presheaf.map (homOfLE hWU).op).hom r) := by
      intro r
      exact (congrArg (fun k => k.hom r) (t.G.hom.map_appLE (hWW i) (homOfLE hWU).op)).symm
    rw [e, e, hcomp i (hWW i), hD]
  · have hr : ∀ z, (spMap φ ≫ GlobalTheory.LogKS.chart U) z ∈ W.1 := by
      intro z
      rw [← hg₀]
      have hz : g₀ z ∈ O := hO' (show z ∈ (⊤ : (Sp S).Opens) from trivial)
      exact hWW i (inf_le_left (a := Wc i) (b := Wc i') (hO hz))
    obtain ⟨φ', hfac⟩ := exists_factor U W hWU φ hr
    have hg₀' : g₀ ≫ t.G.hom = spMap φ' ≫ GlobalTheory.LogKS.chart W := by
      rw [hg₀, hfac, ← spMap_comp'', Category.assoc, chart_res']
    have := htest i i' O hO f S φ' g₀ w hg₀' hO' fun a => by
      obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, spMap_comp'', dualMap_comp'', ← hfac]
    rw [this]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hfac]
    rfl

end GlobalTheory.LogKSUp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerInteriorAffineOpenStatement

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

theorem _root_.GlobalTheory.T.exists_kodairaSpencer_interior_affine_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : Y.X.affineOpens), W.1 ≤ interior Y → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, W.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart W) (v i)) → (∀ w, IsTanAtG Y.t (chart W) w → ∃! cf : Fin n → Γ(Y.X, W.1), IsCombAtG Y.t (chart W) v cf w) → ∀ D : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1), ∃ Θ, IsKS Y.t (interior Y) W v D Θ := by
  first | exact @GlobalTheory.KSInterior.exists_isKS_interior | exact GlobalTheory.KSInterior.exists_isKS_interior | (intros; apply GlobalTheory.KSInterior.exists_isKS_interior <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfInterior

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

namespace GlobalTheory.AffOff

theorem isAffineOpen_inf_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ U : Y.X.affineOpens, IsAffineOpen (U.1 ⊓ interior Y) := by
  intro E _ _ _ H Dw l Xo c Y h U
  have hs := snc_gen_iff.1 h
  unfold boundary at hs
  set V := interior Y with hVdef
  have key : ∀ y : Y.X, ∃ W : Y.X.Opens, y ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (V.ι ⁻¹ᵁ W) := by
    intro y
    obtain ⟨-, W, hy, n, f, J, -, hI⟩ := hs y
    have e : W.1 ⊓ V = Y.X.basicOpen (∏ i ∈ J, f i) := by
      ext z
      constructor
      · rintro ⟨hW, hV⟩
        by_contra hz
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
          exact hz
        rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
        exact this hV
      · intro hz
        have hW : z ∈ W.1 := Y.X.basicOpen_le _ hz
        refine ⟨hW, by_contra fun hV ↦ ?_⟩
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
          exact hV
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span,
          Scheme.zeroLocus_singleton] at this
        exact this hz
    refine ⟨W.1, hy, W.2, ?_⟩
    rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_comm, e]
    exact W.2.basicOpen _
  have : IsAffineHom V.ι := isAffineHom_of_forall_exists_isAffineOpen _ key
  have h2 := U.2.preimage V.ι
  rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] at h2
  rwa [inf_comm]

end GlobalTheory.AffOff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerRegularFramedAffine

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

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KReg

theorem exists_res_eq {X : Scheme.{0}} (U W : X.affineOpens) (V : X.Opens) (hW : W.1 = U.1 ⊓ V) (θ : Γ(X, W.1))
    (h : ∀ m : Ideal Γ(X, U.1), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ X.basicOpen f) ∧ x ∉ V) →
      ∃ g ∉ m, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s =
        (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * θ) :
    ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = θ := by
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (X.presheaf.map (homOfLE hWU).op).hom := ⟨_, rfl⟩
  have hres : ∀ {A B C : X.Opens} (h1 : B ≤ A) (h2 : C ≤ B) (h3 : C ≤ A) (z : Γ(X, A)),
      (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom z) =
        (X.presheaf.map (homOfLE h3).op).hom z := fun h1 h2 h3 z => by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  let J : Ideal Γ(X, U.1) :=
    { carrier := {g | ∃ s : Γ(X, U.1), ρ s = ρ g * θ}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := fun {g g'} ⟨s, hs⟩ ⟨s', hs'⟩ => ⟨s + s', by rw [map_add (f := _), map_add (f := _), hs, hs', add_mul]⟩
      smul_mem' := fun r g ⟨s, hs⟩ => ⟨r * s, by rw [smul_eq_mul, map_mul, map_mul, hs, _root_.mul_assoc]⟩ }
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hne
    let p : PrimeSpectrum Γ(X, U.1) := ⟨m, hm.isPrime⟩
    have hxU : U.2.fromSpec p ∈ U.1 := by
      have : U.2.fromSpec p ∈ Set.range U.2.fromSpec := ⟨p, rfl⟩
      rwa [U.2.range_fromSpec] at this
    have hxf : ∀ f, U.2.fromSpec p ∈ X.basicOpen f ↔ f ∉ m := fun f => by
      change p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f ↔ _
      rw [U.2.fromSpec_preimage_basicOpen]; rfl
    by_cases hxV : U.2.fromSpec p ∈ V
    · obtain ⟨g, hgW, hxg⟩ := U.2.exists_basicOpen_le (V := W.1) ⟨U.2.fromSpec p, hW ▸ ⟨hxU, hxV⟩⟩ hxU
      have hgm : g ∉ m := (hxf g).1 hxg
      apply hgm
      haveI := U.2.isLocalization_basicOpen g
      obtain ⟨⟨s, ⟨_, N, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers g)
        ((X.presheaf.map (homOfLE hgW).op).hom θ)
      have hbo : X.basicOpen (ρ g) ≤ X.basicOpen g := by
        rw [hρ, Scheme.basicOpen_res]; exact inf_le_right
      have e3 : ∀ z, (X.presheaf.map (homOfLE hgW).op).hom (ρ z) =
          algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) z := fun z => by
        rw [hρ]; exact hres hWU hgW (hgW.trans hWU) z
      have hz : (X.presheaf.map (homOfLE hgW).op).hom (ρ g ^ N * θ - ρ s) = 0 := by
        rw [map_sub, map_mul, map_pow, e3, e3, ← map_pow, mul_comm, hs, sub_self]
      have hz' : (X.presheaf.map (homOfLE (X.basicOpen_le (ρ g))).op).hom (ρ g ^ N * θ - ρ s) = 0 := by
        have := congrArg (X.presheaf.map (homOfLE hbo).op).hom hz
        rwa [map_zero, hres hgW hbo (X.basicOpen_le (ρ g))] at this
      obtain ⟨M, hM⟩ := AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X
        W.2.isCompact (ρ g ^ N * θ - ρ s) (ρ g) hz'
      refine hm.isPrime.mem_of_pow_mem (M + N) (hJm ⟨g ^ M * s, ?_⟩)
      rw [map_mul, map_pow, map_pow, pow_add]
      linear_combination (-1 : Γ(X, W.1)) * hM
    · obtain ⟨g, hgm, s, hs⟩ := h m hm ⟨_, hxU, fun f hf hx => (hxf f).1 hx hf, hxV⟩
      exact hgm (hJm ⟨s, hρ ▸ hs⟩)
  obtain ⟨s, hs⟩ : (1 : Γ(X, U.1)) ∈ J := hJ ▸ Submodule.mem_top
  exact ⟨s, by rw [← hρ, hs, map_one, _root_.one_mul]⟩

theorem exists_der_res {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) :
    ∃ DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1), ∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) =
      (X.presheaf.map (homOfLE hW).op).hom (D r) := by
  set ρ := (X.presheaf.map (homOfLE hW).op).hom with hρ
  letI : Algebra Γ(X, U.1) Γ(X, W.1) := ρ.toAlgebra
  have h1 : IsOpenImmersion (chart W) := W.2.isOpenImmersion_fromSpec
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1))) ≫ chart U = chart W :=
    GlobalTheory.LogKSDiv.GenChange.chart_res U W hW
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1))) ≫ chart U) := e ▸ h1
  have : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1)))) :=
    IsOpenImmersion.of_comp _ (chart U)
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1)))) := inferInstance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hs
  have : Algebra.Smooth Γ(X, U.1) Γ(X, W.1) := RingHom.smooth_algebraMap.1 hs
  let g : Γ(X, U.1) →+* DualNumber Γ(X, W.1) :=
    { toFun := fun r => TrivSqZeroExt.inl (ρ r) + TrivSqZeroExt.inr (ρ (D r))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz] <;> ring }
  letI : Algebra Γ(X, U.1) (DualNumber Γ(X, W.1)) := g.toAlgebra
  let π : DualNumber Γ(X, W.1) →ₐ[Γ(X, U.1)] Γ(X, W.1) :=
    { (TrivSqZeroExt.fstHom Γ(X, W.1) Γ(X, W.1) Γ(X, W.1)).toRingHom with
      commutes' := fun r => by simp [g, RingHom.algebraMap_toAlgebra] }
  have hsur : Function.Surjective π := fun s => ⟨TrivSqZeroExt.inl s, rfl⟩
  have hk : IsNilpotent (RingHom.ker (π : DualNumber Γ(X, W.1) →+* Γ(X, W.1))) := by
    refine ⟨2, ?_⟩
    rw [Submodule.zero_eq_bot, eq_bot_iff, pow_two]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Submodule.mem_bot]
    ext <;> simp [ha', hb']
  let l := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id Γ(X, U.1) Γ(X, W.1)) π hsur hk
  have hl1 : ∀ s, (l s).fst = s := fun s =>
    AlgHom.congr_fun (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id Γ(X, U.1) Γ(X, W.1)) π hsur hk) s
  have hl2 : ∀ r, l (ρ r) = g r := fun r => l.commutes r
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun s => (l s).snd, map_zero' := by simp, map_add' := fun x y => by rw [map_add (f := _)]; rfl }) fun a b => ?_,
    fun r => ?_⟩
  · change (l (a * b)).snd = a • (l b).snd + b • (l a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hl1, hl1]
    simp [smul_eq_mul, mul_comm]
  · change (l (ρ r)).snd = _
    rw [hl2]
    simp [g]

theorem exists_isKS_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U, ∃ Θ, IsKS Y.t (interior Y) U v D.1 Θ := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hb hA D
  obtain ⟨W, hW⟩ : ∃ W : Y.X.affineOpens, W.1 = U.1 ⊓ interior Y := ⟨⟨_, GlobalTheory.AffOff.isAffineOpen_inf_interior E H Dw l Xo c Y hsnc U⟩, rfl⟩
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  obtain ⟨DW, hDW⟩ := exists_der_res U W hWU D.1
  obtain ⟨hv', hb'⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t (Y.X.presheaf.map (homOfLE hWU).op).hom
    (chart U) n v hv hb
  rw [GlobalTheory.LogKSDiv.GenChange.chart_res U W hWU] at hv' hb'
  obtain ⟨ΘW, hΘW⟩ := GlobalTheory.T.exists_kodairaSpencer_interior_affine_open E H Dw l Xo c Y W (hW.le.trans inf_le_right) n _ hv' hb' DW
  have key := fun (m : Ideal Γ(Y.X, U.1)) (hm : m.IsMaximal) hx =>
    GlobalTheory.T.kodairaSpencer_regular_near_rigid_boundary_point E H Dw l Xo c Y hpq hsm hsnc hrig U W hW n v hv hb D DW ΘW hDW hΘW m hm hx
  choose Θ hΘ using fun a b => exists_res_eq U W (interior Y) hW (ΘW a b) fun m hm hx =>
    (key m hm hx).imp fun g hg => ⟨hg.1, hg.2 a b⟩
  refine ⟨Θ, GlobalTheory.LogKSUp.isKS_of_inf E H Y.X Y.t (interior Y) U W hW n v D.1 DW Θ hDW ?_⟩
  convert hΘW using 1
  ext a b
  exact hΘ a b

end GlobalTheory.KReg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerRegularFramedAffineStatement

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

theorem _root_.GlobalTheory.T.exists_kodairaSpencer_regular_framed_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U, ∃ Θ, IsKS Y.t (interior Y) U v D.1 Θ := by
  first | exact @GlobalTheory.KReg.exists_isKS_regular | exact GlobalTheory.KReg.exists_isKS_regular | (intros; apply GlobalTheory.KReg.exists_isKS_regular <;> assumption)
end
end

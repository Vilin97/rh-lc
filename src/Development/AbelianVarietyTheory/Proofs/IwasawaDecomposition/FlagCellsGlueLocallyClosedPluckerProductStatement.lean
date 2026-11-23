module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Algebra.Azumaya.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Order.CompletePartialOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellIsClosedInLeadingMinorOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeInterCellOpenSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRing

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLESpMapFromSpec

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb

namespace GlobalTheory.FlagEmb.CellOpen

variable {O : Type} [CommRing O] {X P : Scheme.{0}} {N : ℕ} {k : Type} [Field k]

theorem top_le_of_mem {W : (Sp k).Opens} {x : Sp k} (hx : x ∈ W) : ⊤ ≤ W := fun y _ => by
  have : y = x := Subsingleton.elim (α := PrimeSpectrum k) y x
  exact this ▸ hx

theorem mem_basicOpen_fnOn (x : Sp k) (a : k) : x ∈ (Sp k).basicOpen (fnOn ⊤ a) ↔ a ≠ 0 := by
  rw [basicOpen_fnOn, top_inf_eq, mem_spOpen]
  have : x.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum k) x ⊥)
  rw [this, Ideal.mem_bot]

theorem appLE_spMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) {A : Type} [CommRing A] (φ : Γ(X, U) →+* A)
    {x : Sp A ⟶ X} (hx : x = spMap φ ≫ hU.fromSpec) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    (x.appLE U ⊤ h).hom a = fnOn ⊤ (φ a) := by
  subst hx
  have e := appLE_appLE (spMap φ) hU.fromSpec hU.fromSpec_preimage_self.ge (le_rfl : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) a
  refine e.symm.trans ?_
  rw [fromSpec_appLE_self]
  have e2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (R := Γ(X, U)) (S := .of A) (CommRingCat.ofHom φ))
  refine Eq.trans ?_ (congrArg (resG (Sp A) (le_top : (⊤ : (Sp A).Opens) ≤ ⊤)) e2.symm)
  rfl

def sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) (r : Fin (N + 1)) :
    Γ(P, p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r) :=
  ∑ q, (p0.appLE U _ inf_le_left).hom (a q) * pullRatio g _ r inf_le_right q

theorem appLE_sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U) (a : Fin (N + 1) → Γ(X, U))
    (r : Fin (N + 1)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)) :
    v r ≠ 0 ∧ (z.appLE _ ⊤ h).hom (sec p0 g U a r) = fnOn ⊤ ((∑ q, φ (a q) * v q) / v r) := open MvPolynomial GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjFrac in by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := O)
  have pre : pt b v hv ⁻¹ᵁ chart O N r = spOpen (v r) := by
    change ProjPoint.ofHom (grading O N) (eval₂Hom b v) (map_irrelevant_eval₂Hom b hv) ⁻¹ᵁ
      Proj.basicOpen (grading O N) (MvPolynomial.X r) = _
    rw [ProjPoint.ofHom_preimage_basicOpen _ _ _ one_pos (isHomogeneous_X O r), eval₂Hom_X']
    rfl
  have from_chart : (isAffineOpen_chart O N r).fromSpec =
      Spec.map (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos := by
    rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
    refine (Category.id_comp _).symm.trans (congrArg (· ≫ _) ?_)
    exact (Proj.basicOpenIsoSpec (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).hom_inv_id.symm
  have away_ratio (q : Fin (N + 1)) :
      (Proj.awayToSection (grading O N) (MvPolynomial.X r)).hom (ratioAway O N r q) = ratio O N r q := by
    rw [ratioAway, awayToSection_mk]
    exact frac_eq (by ring)
  have h2 : ⊤ ≤ pt b v hv ⁻¹ᵁ chart O N r := hz ▸ h.trans (z.preimage_mono inf_le_right)
  have hr : v r ≠ 0 := by
    have := h2 (Set.mem_univ (IsLocalRing.closedPoint k))
    rw [pre] at this
    intro e
    exact (mem_spOpen.1 this) (e ▸ zero_mem _)
  have ratio_mul (q : Fin (N + 1)) :
      pullRatio (pt b v hv) ⊤ r h2 q * fnOn ⊤ (v r) = fnOn ⊤ (v q) := by
    have hu' : IsUnit (eval₂Hom b v (MvPolynomial.X r)) := by rw [eval₂Hom_X']; exact IsUnit.mk0 _ hr
    have h4 := ProjPoint.awayLift_mk_mul (grading O N) (eval₂Hom b v) hu' (X_mem O N r) 1 (MvPolynomial.X q) (X_mem O N q)
    have he : pt b v hv = spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫ _ :=
      ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem O N r) hu'
    have : IsIso (Proj.awayToSection (grading O N) (MvPolynomial.X r)) :=
      (Proj.basicOpenIsoAway (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).isIso_hom
    have he2 : spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos =
        ofChartHom r (inv (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
          CommRingCat.ofHom (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
          (Scheme.ΓSpecIso (.of k)).inv) := by
      rw [ofChartHom, from_chart, ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
    rw [pullRatio_of_eq he h2 (he ▸ h2), pullRatio_of_eq he2 _ (ofChartHom_preimage _ _),
      pullRatio, ofChartHom_appLE, ← away_ratio, ← CommRingCat.comp_apply, IsIso.hom_inv_id_assoc,
      ]
    change (Scheme.ΓSpecIso (.of k)).inv.hom
      (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu' (ratioAway O N r q)) * _ = _
    rw [← resG_self (X := Sp k) le_top ((Scheme.ΓSpecIso (.of k)).inv.hom _)]
    change fnOn ⊤ _ * fnOn ⊤ _ = fnOn ⊤ _
    rw [← map_mul]
    exact congrArg _ (by simpa only [ratioAway, eval₂Hom_X', pow_one] using h4)
  refine ⟨hr, ((IsUnit.mk0 _ hr).map (fnOn ⊤)).mul_right_cancel ?_⟩

  rw [← map_mul, div_mul_cancel₀ _ hr, sec, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, map_mul, appLE_appLE, appLE_spMap_fromSpec hU φ hφ, appLE_pullRatio, pullRatio_of_eq hz _ h2, mul_assoc,
    ratio_mul]

def linOpen (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) : P.Opens :=
  ⨆ r, P.basicOpen (sec p0 g U a r)

theorem mem_linOpen_iff (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Fin (N + 1) → Γ(X, U)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (x : Sp k) :
    z x ∈ linOpen p0 g U a ↔ ∑ q, φ (a q) * v q ≠ 0 := by
  have key : ∀ r (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)),
      z x ∈ P.basicOpen (sec p0 g U a r) ↔ ∑ q, φ (a q) * v q ≠ 0 := fun r h => by
    obtain ⟨hr, e⟩ := appLE_sec p0 g hU a r z φ hφ b v hv hz h
    have e2 := Scheme.basicOpen_appLE z ⊤ _ h (sec p0 g U a r)
    rw [top_inf_eq] at e2
    refine (iff_of_eq (congrArg (x ∈ ·) e2)).symm.trans ?_
    refine (iff_of_eq (congrArg (fun t => x ∈ (Sp k).basicOpen t) e)).trans ?_
    rw [mem_basicOpen_fnOn, div_ne_zero_iff, and_iff_left hr]
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := Opens.mem_iSup.1 hx
    exact (key r (top_le_of_mem (x := x) (P.basicOpen_le _ hr))).1 hr
  · intro hx
    obtain ⟨r, hr⟩ := exists_mem_chart O N (g (z x))
    refine Opens.mem_iSup.2 ⟨r, (key r (top_le_of_mem (x := x) ⟨?_, hr⟩)).2 hx⟩
    change x ∈ (z ≫ p0) ⁻¹ᵁ U
    rw [hφ, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    trivial

theorem exists_isCellOpen (O : Type) [CommRing O] (X P : Scheme.{0}) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ)
    (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (U : X.affineOpens)
    (D : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) : ∃ W : P.Opens, IsCellOpen p0 p U D w W := by
  let F : (Σ τ : T, Fin (m τ + 1)) → P.Opens := fun i =>
    linOpen p0 (p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))) U.1 (lform D (wLet w ∘ std i.1 i.2 (Nat.le_of_lt_succ i.2.2)))
  refine ⟨p0 ⁻¹ᵁ U.1 ⊓ ⟨⋂ i, (F i : Set P), isOpen_iInter_of_finite fun i => (F i).2⟩, fun k _ z => ⟨fun h => ?_, ?_⟩⟩
  · have h1 : Set.range (z ≫ p0) ⊆ Set.range U.2.fromSpec := by
      rw [U.2.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact (h ⟨x, rfl⟩).1
    have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    let l := IsOpenImmersion.lift U.2.fromSpec (z ≫ p0) h1
    have hφ : z ≫ p0 = spMap (Spec.preimage l).hom ≫ U.2.fromSpec :=
      (IsOpenImmersion.lift_fac _ _ h1).symm.trans (congrArg (· ≫ _) (Spec.map_preimage l).symm)
    refine ⟨(Spec.preimage l).hom, hφ, fun τ j hj b v hv hz => ?_⟩
    refine (mem_linOpen_iff p0 _ U.2 _ z _ hφ b v hv hz (IsLocalRing.closedPoint k)).1 ?_
    exact Set.mem_iInter.1 (h ⟨_, rfl⟩).2 ⟨τ, j, Nat.lt_succ_of_le hj⟩
  · rintro ⟨φ, hφ, H⟩ _ ⟨x, rfl⟩
    refine ⟨?_, Set.mem_iInter.2 fun i => ?_⟩
    · change x ∈ (z ≫ p0) ⁻¹ᵁ U.1
      rw [hφ, Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_self]
      trivial
    · let y := z ≫ p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))
      obtain ⟨v, hv, e⟩ := exists_eq_pt (Spec.preimage (y ≫ PSpace.str _ _)).hom y (Spec.map_preimage _).symm
      exact (mem_linOpen_iff p0 _ U.2 _ z φ hφ _ v hv e x).2 (H _ _ _ _ v hv e)

end GlobalTheory.FlagEmb.CellOpen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImmersionOfClosedPieces

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.MemberGlue

theorem exists_immersion_of_closed_pieces : ∀ (P : Scheme.{0}) (ι : Type) [Finite ι] (C : ι → Scheme.{0}) [∀ a, IsAffine (C a)] [∀ a, IsReduced (C a)] (h : ∀ a, C a ⟶ P) (W : ι → P.Opens) (h' : ∀ a, C a ⟶ (W a).toScheme), IsLocallyNoetherian P → (∀ a, h' a ≫ (W a).ι = h a) → (∀ a, IsClosedImmersion (h' a)) → (∀ a a', Set.range (h a') ∩ (W a : Set P) ⊆ Set.range (h a)) → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ a, C a ⟶ F), IsImmersion f ∧ (∀ a, IsOpenImmersion (i a)) ∧ (∀ a, i a ≫ f = h a) ∧ ∀ x : F, ∃ a, x ∈ Set.range (i a) := by
  intro P ι _ C _ _ h W h' _ hh hcl hag
  have hpt : ∀ a c, (W a).ι (h' a c) = h a c := fun a c => by rw [← hh a]; rfl
  let U : P.Opens := ⨆ a, W a
  let Φ : Set P := ⋃ a, Set.range (h a)
  let O : ι → Set P := fun a => (W a).ι '' (Set.range (h' a))ᶜ
  have hO : ∀ a, IsOpen (O a) := fun a =>
    (W a).ι.isOpenEmbedding.isOpenMap _ (h' a).isClosedEmbedding.isClosed_range.isOpen_compl
  have hW : ∀ a c, h a c ∈ (W a : Set P) := fun a c => by
    rw [← hpt a c]; exact (h' a c).2
  have hU : ∀ a, (W a : Set P) ⊆ U := fun a =>
    SetLike.coe_subset_coe.mpr (le_iSup W a)
  have hΦ : U.ι ⁻¹' Φ = (U.ι ⁻¹' ⋃ a, O a)ᶜ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hx hxO
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, w, hw, e⟩ := Set.mem_iUnion.mp hxO |>.imp fun _ h => h
      have h1 : U.ι x ∈ Set.range (h a') ∩ (W a : Set P) :=
        ⟨⟨c', hc'⟩, e ▸ w.2⟩
      obtain ⟨c, hc⟩ := hag a a' h1
      exact hw ⟨c, (W a).ι.isOpenEmbedding.injective ((hpt a c).trans (hc.trans e.symm))⟩
    · intro hx
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
      have h2 : (⟨x.1, ha⟩ : (W a).toScheme) ∈ Set.range (h' a) := by
        by_contra hn
        exact hx (Set.mem_iUnion.mpr ⟨a, ⟨x.1, ha⟩, hn, rfl⟩)
      obtain ⟨c, hc⟩ := h2
      exact Set.mem_iUnion.mpr ⟨a, c, by rw [← hpt a c, hc]; rfl⟩
  let Z : TopologicalSpace.Closeds U.toScheme := ⟨U.ι ⁻¹' Φ, by
    rw [hΦ]
    exact ((isOpen_iUnion hO).preimage U.ι.continuous).isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let g : I.subscheme ⟶ U.toScheme := I.subschemeι
  let f : I.subscheme ⟶ P := g ≫ U.ι
  have hrg : Set.range g = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hfΦ : ∀ x, f x ∈ Φ := fun x => by
    have : g x ∈ (Z : Set U.toScheme) := hrg ▸ ⟨x, rfl⟩
    exact this
  have hfinj : Function.Injective f := f.isEmbedding.injective
  have hrU : ∀ a, Set.range (h a) ⊆ Set.range U.ι := fun a => by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hU a (hW a c)
  let k : ∀ a, C a ⟶ U.toScheme := fun a => IsOpenImmersion.lift U.ι (h a) (hrU a)
  have hk : ∀ a, k a ≫ U.ι = h a := fun a => IsOpenImmersion.lift_fac _ _ _
  have hkZ : ∀ a, Set.range (k a) ⊆ Z := fun a => by
    rintro _ ⟨c, rfl⟩
    change U.ι (k a c) ∈ Φ
    have : U.ι (k a c) = h a c := by rw [← hk a]; rfl
    rw [this]
    exact Set.mem_iUnion.mpr ⟨a, c, rfl⟩
  have hker : ∀ a, g.ker ≤ (k a).ker := fun a => by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ReducedSubgroup.vanishingIdeal_le_ker (k a) Z (hkZ a)
  let i : ∀ a, C a ⟶ I.subscheme := fun a => IsClosedImmersion.lift g (k a) (hker a)
  have hig : ∀ a, i a ≫ g = k a := fun a => IsClosedImmersion.lift_fac _ _ _
  have hif : ∀ a, i a ≫ f = h a := fun a => by
    rw [← hk a, ← hig a, Category.assoc]
  have hipt : ∀ a c, f (i a c) = h a c := fun a c => by rw [← hif a]; rfl
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  refine ⟨I.subscheme, f, i, inferInstance, fun a => ?_, hif, fun x => ?_⟩
  · let V : I.subscheme.Opens := f ⁻¹ᵁ W a
    have hiV : Set.range (i a) ⊆ Set.range V.ι := by
      rintro _ ⟨c, rfl⟩
      rw [Scheme.Opens.range_ι]
      change f (i a c) ∈ W a
      rw [hipt]
      exact hW a c
    have hrW : Set.range (V.ι ≫ f) ⊆ Set.range (W a).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2
    let j : C a ⟶ V.toScheme := IsOpenImmersion.lift V.ι (i a) hiV
    have hj : j ≫ V.ι = i a := IsOpenImmersion.lift_fac _ _ _
    let r : V.toScheme ⟶ (W a).toScheme := IsOpenImmersion.lift (W a).ι (V.ι ≫ f) hrW
    have hr : r ≫ (W a).ι = V.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have hjr : j ≫ r = h' a := by
      rw [← cancel_mono (W a).ι, Category.assoc, hr, reassoc_of% hj, hif, hh]
    have : Mono r := by
      have : Mono (r ≫ (W a).ι) := by rw [hr]; infer_instance
      exact mono_of_mono r (W a).ι
    have : IsClosedImmersion (j ≫ r) := by rw [hjr]; infer_instance
    have : IsClosedImmersion j := IsClosedImmersion.of_comp j r
    have : Surjective j := ⟨fun y => by
      have hy : f (V.ι y) ∈ (W a : Set P) := y.2
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp (hfΦ (V.ι y))
      obtain ⟨c, hc⟩ := hag a a' ⟨⟨c', hc'⟩, hy⟩
      refine ⟨c, V.ι.isOpenEmbedding.injective (hfinj ?_)⟩
      have : V.ι (j c) = i a c := by rw [← hj]; rfl
      rw [this, hipt, hc]⟩
    have : IsIso j := isIso_of_isClosedImmersion_of_surjective j
    rw [← hj]
    infer_instance
  · obtain ⟨a, c, hc⟩ := Set.mem_iUnion.mp (hfΦ x)
    exact ⟨a, c, hfinj ((hipt a c).trans hc)⟩

end GlobalTheory.MemberGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellIsClosedInLeadingMinorOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.flagCell_isClosed_in_leadingMinor_open : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → IsNoetherianRing O → IsProjOver s → ∀ b w (W : P.Opens), IsCellOpen p0 p (V b) (D b) w W → ∃ h' : Sp (CR m (V b)) ⟶ W.toScheme, h' ≫ W.ι = h b w ∧ IsClosedImmersion h' := by
  first | exact @GlobalTheory.FlagEmb.CellClosed.cell_closed | exact GlobalTheory.FlagEmb.CellClosed.cell_closed | (intros; apply GlobalTheory.FlagEmb.CellClosed.cell_closed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProduct

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.FlagEmb.cells_glue : ∀ (O K : Type) [CommRing O] [IsNoetherianRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover β s V α c D → IsPlk β s V α c p0 p h → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), IsImmersion f ∧ (∀ b w, IsOpenImmersion (i b w)) ∧ (∀ b w, i b w ≫ f = h b w) ∧ ∀ x : F, ∃ b w, x ∈ Set.range (i b w) := by
  intro O K _ _ _ β X s T _ m M B _ V α c D P p0 p h hs hX hC hP
  have hLN : ∀ {Y : Scheme.{0}} (g : Y ⟶ Sp O), IsProjOver g → IsLocallyNoetherian Y := by
    intro Y g hg
    obtain ⟨N, ι, _, rfl⟩ := hg
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str O N)
  haveI : IsLocallyNoetherian X := hLN s hs
  haveI : IsLocallyNoetherian P := hLN _ hP.proj
  have hW : ∀ b w, ∃ W, IsCellOpen p0 p (V b) (D b) w W := fun b w =>
    GlobalTheory.FlagEmb.CellOpen.exists_isCellOpen O X P T m M p0 p (V b) (D b) w
  choose W hW using hW
  have hcl := fun b w => GlobalTheory.T.flagCell_isClosed_in_leadingMinor_open O K β X s T m M B V α c D P p0 p h hC hP inferInstance hs b w (W b w) (hW b w)
  choose h' hh' hci using hcl
  have hred : ∀ b, AlgebraicGeometry.IsReduced (Sp (CR m (V b))) := by
    intro b
    have hn := (GlobalTheory.FlagEmb.cell_smooth_normal X T m (V b) hX).2
    haveI := fun x => (hn x).1
    exact isReduced_of_isReduced_stalk _
  let ι := B × Pm m
  haveI : Finite (Pm m) := Pi.finite
  haveI : ∀ a : ι, IsAffine (Sp (CR m (V a.1))) := fun a => inferInstance
  haveI : ∀ a : ι, AlgebraicGeometry.IsReduced (Sp (CR m (V a.1))) := fun a => hred a.1
  obtain ⟨F, f, i, hf, hio, hcomp, hcov⟩ := GlobalTheory.MemberGlue.exists_immersion_of_closed_pieces P ι
    (fun a => Sp (CR m (V a.1))) (fun a => h a.1 a.2) (fun a => W a.1 a.2) (fun a => h' a.1 a.2) inferInstance
    (fun a => hh' a.1 a.2) (fun a => hci a.1 a.2)
    (fun a a' => GlobalTheory.FlagEmb.Overlap.range_inter_cellOpen_subset O K β X s T m M B V α c D P p0 p h hC hP a.1 a.2
      (W a.1 a.2) (hW a.1 a.2) a'.1 a'.2)
  refine ⟨F, f, fun b w => i (b, w), hf, fun b w => hio (b, w), fun b w => hcomp (b, w), fun x => ?_⟩
  obtain ⟨a, ha⟩ := hcov x
  exact ⟨a.1, a.2, ha⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProductStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.flagCells_glue_locallyClosed_pluckerProduct : ∀ (O K : Type) [CommRing O] [IsNoetherianRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover β s V α c D → IsPlk β s V α c p0 p h → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), IsImmersion f ∧ (∀ b w, IsOpenImmersion (i b w)) ∧ (∀ b w, i b w ≫ f = h b w) ∧ ∀ x : F, ∃ b w, x ∈ Set.range (i b w) := by
  first | exact @GlobalTheory.FlagEmb.cells_glue | exact GlobalTheory.FlagEmb.cells_glue | (intros; apply GlobalTheory.FlagEmb.cells_glue <;> assumption)
end
end

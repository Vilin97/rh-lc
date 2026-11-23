module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleOfFiniteAffineSubcoverStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1FiniteAffineOpenStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover : ∀ (Z : Scheme.{0}) (J : Type) (W : J → Z.Opens) (S : Set J), (∀ i, W i ≤ ⨆ a ∈ S, W a) → ∀ d : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W d → ∀ h₀ : ∀ i, Γ(Z, W i), (∀ a ∈ S, ∀ b ∈ S, d a b = resG Z inf_le_left (h₀ a) - resG Z inf_le_right (h₀ b)) → ∃ h : ∀ i, Γ(Z, W i), ∀ i i', d i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechFin.isCob_of_isCob_subcover | exact GlobalTheory.CechFin.isCob_of_isCob_subcover | (intros; apply GlobalTheory.CechFin.isCob_of_isCob_subcover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_transfer {Z Z' : Scheme.{0}} {J : Type} (W : J → Z.Opens) (W' : J → Z'.Opens)
    (R : Type) [CommRing R]
    (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) (act' : ∀ i i' : J, R →+* Γ(Z', W' i ⊓ W' i'))
    (φ1 : ∀ i, Γ(Z, W i) →+* Γ(Z', W' i))
    (φ2 : ∀ i i', Γ(Z, W i ⊓ W i') →+* Γ(Z', W' i ⊓ W' i'))
    (φ3 : ∀ i i' i'', Γ(Z, W i ⊓ W i' ⊓ W i'') →+* Γ(Z', W' i ⊓ W' i' ⊓ W' i''))
    (h1 : ∀ i, Function.Surjective (φ1 i))
    (h2 : ∀ i i', Function.Bijective (φ2 i i'))
    (h3 : ∀ i i' i'', Function.Injective (φ3 i i' i''))
    (hl : ∀ i i' x, φ2 i i' (resG Z inf_le_left x) = resG Z' inf_le_left (φ1 i x))
    (hr : ∀ i i' x, φ2 i i' (resG Z inf_le_right x) = resG Z' inf_le_right (φ1 i' x))
    (ha : ∀ i i' i'' x, φ3 i i' i'' (resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') x) =
      resG Z' (inf_le_left : W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i') (φ2 i i' x))
    (hb : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i' ⊓ W' i'') (φ2 i' i'' x))
    (hc : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i'') (φ2 i i'' x))
    (hact : ∀ i i' r, φ2 i i' (act i i' r) = act' i i' r) :
    CechFG W' R act' → CechFG W R act := by
  rintro ⟨N, e', he', hc'⟩
  choose g hg using fun (k : Fin N) (i i' : J) => (h2 i i').2 (e' k i i')
  refine ⟨N, g, ?_, ?_⟩
  · intro k i i' i''
    apply h3 i i' i''
    have := he' k i i' i''
    rw [map_add (f := _), ha, hb, hc, hg, hg, hg]
    exact this
  · intro c hcoc
    obtain ⟨r, h', hh⟩ := hc' (fun i i' => φ2 i i' (c i i')) (by
      intro i i' i''
      have := congrArg (φ3 i i' i'') (hcoc i i' i'')
      rw [map_add (f := _), ha, hb, hc] at this
      exact this)
    choose h hh1 using fun i => h1 i (h' i)
    refine ⟨r, h, fun i i' => (h2 i i').1 ?_⟩
    have e1 := hh i i'

    rw [map_add (f := _), map_sub, map_sum, hl, hr, hh1, hh1]
    simp only [map_mul, hact, hg]
    exact e1

theorem appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {O₁ O₂ : Y.Opens} {V₁ V₂ : X.Opens} (hO : O₂ ≤ O₁)
    (hV : V₂ ≤ V₁) (e₁ : V₁ ≤ f ⁻¹ᵁ O₁) (e₂ : V₂ ≤ f ⁻¹ᵁ O₂) (x : Γ(Y, O₁)) :
    (f.appLE O₂ V₂ e₂).hom (resG Y hO x) = resG X hV ((f.appLE O₁ V₁ e₁).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] {O : Y.Opens}
    (hO : O ≤ f.opensRange) {V : X.Opens} (hV : V = f ⁻¹ᵁ O) (e : V ≤ f ⁻¹ᵁ O) :
    Function.Bijective (f.appLE O V e).hom := by
  subst hV
  rw [Scheme.Hom.appLE_eq_app]
  haveI := f.isIso_app O hO
  exact (asIso (f.app O)).commRingCatIsoToRingEquiv.bijective

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem preimage_inf' {X Y : Scheme.{0}} (f : X ⟶ Y) (A B : Y.Opens) :
    f ⁻¹ᵁ (A ⊓ B) = f ⁻¹ᵁ A ⊓ f ⁻¹ᵁ B := by
  ext x; simp

theorem appLE_act {G X : Scheme.{0}} (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (O : G.Opens)
    (V : (pullback p hU.fromSpec).Opens) (hO : O ≤ p ⁻¹ᵁ U)
    (e : V ≤ pullback.fst p hU.fromSpec ⁻¹ᵁ O) (r : Γ(X, U)) :
    ((pullback.fst p hU.fromSpec).appLE O V e).hom ((p.appLE U O hO).hom r) =
      (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) V).hom r := by
  have e' : V ≤ (pullback.snd p hU.fromSpec ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [← pullback.condition]; exact e.trans (Scheme.Hom.preimage_mono _ hO)
  have key : (pullback.snd p hU.fromSpec ≫ hU.fromSpec).appLE U V e' =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (pullback.snd p hU.fromSpec).appLE ⊤ V le_top := by
    rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self, Category.assoc]
    exact congrArg ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ ·) (Scheme.Hom.map_appLE _ _ _)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq pullback.condition _ _ _ e', key]
  rfl

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_baseChange_affineOpen (G X : Scheme.{0}) (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) :
    CechFG (fun i => pullback.fst p hU.fromSpec ⁻¹ᵁ W i) Γ(X, U)
        (fun i i' => (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) _).hom) →
      CechFG W Γ(X, U) (fun i i' => (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  have hR : ∀ O : G.Opens, O ≤ p ⁻¹ᵁ U → O ≤ (pullback.fst p hU.fromSpec).opensRange := by
    intro O hO
    rw [Scheme.Hom.opensRange_pullbackFst, IsAffineOpen.opensRange_fromSpec]
    exact hO
  have h2e : ∀ A B : G.Opens, pullback.fst p hU.fromSpec ⁻¹ᵁ A ⊓ pullback.fst p hU.fromSpec ⁻¹ᵁ B =
      pullback.fst p hU.fromSpec ⁻¹ᵁ (A ⊓ B) := fun A B => (preimage_inf' _ A B).symm
  refine cechFG_of_transfer W _ _ _ _
    (fun i => ((pullback.fst p hU.fromSpec).appLE (W i) _ le_rfl).hom)
    (fun i i' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i') _ (h2e _ _).le).hom)
    (fun i i' i'' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i' ⊓ W i'') _
      (by rw [h2e, h2e])).hom)
    (fun i => (appLE_bijective _ (hR _ (hWU i)) rfl _).2)
    (fun i i' => appLE_bijective _ (hR _ (inf_le_left.trans (hWU i))) (h2e _ _) _)
    (fun i i' i'' => (appLE_bijective _ (hR _ (inf_le_left.trans (inf_le_left.trans (hWU i))))
      (by rw [h2e, h2e]) _).1)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' r => appLE_act p U hU _ _ _ _ r)

theorem cechFG_of_baseChange_affine (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type)
    (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1) :
    CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1)
        (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) →
      CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) :=
  cechFG_of_baseChange_affineOpen G X p U.1 U.2 J W hWU

end GlobalTheory.CechTr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

theorem _root_.GlobalTheory.T.cech_finite_generation_of_affine_base_change : ∀ (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1) (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) → CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  first | exact @GlobalTheory.CechTr.cechFG_of_baseChange_affine | exact GlobalTheory.CechTr.cechFG_of_baseChange_affine | (intros; apply GlobalTheory.CechTr.cechFG_of_baseChange_affine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSemiAbelianAffineOpenBaseChangeCompactCove

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

namespace GlobalTheory

theorem pullback_fromSpec_compact_affineCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → CompactSpace ↑(pullback t.G.hom U.2.fromSpec : Scheme.{0}) ∧ (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i)) ∧ ⨆ i, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i = ⊤ := by
  intro E _ _ _ H X t hP U J W hW hcov
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hU : IsAffineOpen U.1 := U.2
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : IsOpenImmersion (pullback.fst t.G.hom hU.fromSpec) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd t.G.hom hU.fromSpec)
  · intro I hI
    have := GlobalTheory.isAffineHom_diagonal_of_isSeparated (pullback.snd t.G.hom hU.fromSpec)
    refine GlobalTheory.isAffineOpen_finset_biInf (fun i => ?_) I hI
    have hle : W i ≤ (pullback.fst t.G.hom hU.fromSpec).opensRange := by
      intro x hx
      have hx' : x ∈ t.G.hom ⁻¹ᵁ U.1 := hcov ▸ (le_iSup W i) hx
      have hy : t.G.hom x ∈ Set.range hU.fromSpec := by
        rw [hU.range_fromSpec]; exact hx'
      obtain ⟨y, hy⟩ := hy
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      exact ⟨z, hz⟩
    rw [← (pullback.fst t.G.hom hU.fromSpec).isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hle]
    exact hW i
  · rw [← Scheme.Hom.preimage_iSup, hcov, ← Scheme.Hom.comp_preimage, pullback.condition,
      Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self, Scheme.Hom.preimage_top]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSemiAbelianAffineOpenBaseChangeCompactCoveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

theorem _root_.GlobalTheory.T.properSemiAbelian_affineOpen_baseChange_compact_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → CompactSpace ↑(pullback t.G.hom U.2.fromSpec : Scheme.{0}) ∧ (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i)) ∧ ⨆ i, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i = ⊤ := by
  first | exact @GlobalTheory.pullback_fromSpec_compact_affineCover | exact GlobalTheory.pullback_fromSpec_compact_affineCover | (intros; apply GlobalTheory.pullback_fromSpec_compact_affineCover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1FiniteGenerationAffine

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin
open GlobalTheory.CatCoh GlobalTheory.CechDR

theorem isCoc_sub {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens) {c c' : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCoc W c) (hc' : IsCoc W c') : IsCoc W (fun i i' => c i i' - c' i i') := by
  intro i i' i''
  simp only [map_sub]
  linear_combination hc i i' i'' - hc' i i' i''

theorem cechFG_of_finite (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) [CompactSpace Z]
    (hfin : Module.Finite R (HO1 s)) (J : Type) (W : J → Z.Opens)
    (hD : ∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) (hc : ⨆ i, W i = ⊤) :
    CechFG W R (fun i i' => (secMap s (W i ⊓ W i')).hom) := by
  classical
  have hW : ∀ i, IsAffineOpen (W i) := fun i => by simpa using hD {i} (Finset.singleton_nonempty i)
  have hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i') := fun i i' => by
    have h := hD {i, i'} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_singleton] at h
  have hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'') := fun i i' i'' => by
    have h := hD {i, i', i''} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_insert, Finset.iInf_singleton, ← inf_assoc] at h
  obtain ⟨S, hS⟩ : ∃ S : Finset J, ⨆ i ∈ S, W i = ⊤ := by
    have hcov : (Set.univ : Set Z) ⊆ ⋃ i, (W i : Set Z) := by
      intro x _
      have hx : x ∈ ⨆ i, W i := hc ▸ trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx
    obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set Z)) (fun i => (W i).isOpen) hcov
    refine ⟨S, eq_top_iff.2 fun x _ => ?_⟩
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨hi, hx⟩⟩
  have hsur : ∀ c, IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i i',
      c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
    intro c hcoc
    obtain ⟨f, h₀, hf⟩ := GlobalTheory.T.cechCocycle_of_finite_affine_subcover R Z s J W hW hW2 hD S hS c hcoc
    obtain ⟨h, hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover Z J W (↑S) (fun i => by
        rw [show (⨆ a ∈ (↑S : Set J), W a) = ⨆ a ∈ S, W a from by simp, hS]; exact le_top)
      (fun i i' => c i i' - rho W s hW hW2 f.1 i i') (isCoc_sub W hcoc (rho_isCoc W s hW hW2 hW3 f)) h₀
      (fun a ha b hb => by rw [hf a ha b hb]; ring)
    exact ⟨f, h, fun i i' => by rw [← hh]; ring⟩
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := HO1 s)
  choose fk hfk using fun k => H1.mk_surjective (OAff s) (v k)
  refine ⟨n, fun k => rho W s hW hW2 (fk k).1, fun k => rho_isCoc W s hW hW2 hW3 (fk k), fun c hcoc => ?_⟩
  obtain ⟨f, h, hfh⟩ := hsur c hcoc
  have hmem : H1.mk (OAff s) f ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  have hcl : H1.mk (OAff s) f = H1.mk (OAff s) (∑ k, r k • fk k) := by

    rw [map_sum, ← hr]
    simp only [map_smul, hfk]
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hcl
  have e1 : f.1 = (∑ k, r k • (fk k).1) + d0 (OAff s) g := by
    rw [hg, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    abel
  refine ⟨r, fun i => h i + (-gv s g ⟨W i, hW i⟩), fun i i' => ?_⟩
  rw [hfh, e1, rho_add, rho_sum, rho_d0, map_add (f := _), map_add (f := _)]
  ring

end GlobalTheory.CechFin

open GlobalTheory.CechFin in
theorem GlobalTheory.CechFin.cech_h1_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP hA U J W hWaff hcov hWU
  obtain ⟨hcomp, hD, htop⟩ := GlobalTheory.T.properSemiAbelian_affineOpen_baseChange_compact_cover E H X t hP U J W hWaff hcov
  have hfin := GlobalTheory.T.structure_h1_finite_affine_open E H X t hP U
  exact GlobalTheory.T.cech_finite_generation_of_affine_base_change t.G.left X t.G.hom U J W hWU
    (cechFG_of_finite Γ(X, U.1) (pullback t.G.hom U.2.fromSpec) (pullback.snd t.G.hom U.2.fromSpec) hfin J _ hD htop)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1FiniteGenerationAffineStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cech_h1_finite_generation_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  first | exact @GlobalTheory.CechFin.cech_h1_finite | exact GlobalTheory.CechFin.cech_h1_finite | (intros; apply GlobalTheory.CechFin.cech_h1_finite <;> assumption)
end
end

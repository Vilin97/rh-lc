module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineLineMorphismConstantOfConstOnNonzeroStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreLineOverSurjectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSetOfChartsMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleInvOfFamMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineChartFamiliesAgreeOnOverlap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PuncturedLineOpenCofiniteStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartMapIntoAffineConst

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open Polynomial in
theorem poly_eq_C_of_eq_aeval_invSelf {K : Type} [CommRing K] (p q : K[X])
    (h : algebraMap K[X] (Localization.Away (X : K[X])) p =
      aeval (IsLocalization.Away.invSelf (X : K[X]) : Localization.Away (X : K[X])) q) :
    p = C (p.eval 0) := by
  set L := Localization.Away (X : K[X])
  set n := q.natDegree
  letI : Invertible (algebraMap K[X] L X) :=
    ⟨IsLocalization.Away.invSelf (X : K[X]),
      by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf _, IsLocalization.Away.mul_invSelf _⟩
  have hr : (q.reflect n).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
  have key := eval₂_reflect_mul_pow (algebraMap K L) (algebraMap K[X] L X) n (q.reflect n) hr
  rw [reflect_reflect] at key
  have hev : ∀ r : K[X], eval₂ (algebraMap K L) (algebraMap K[X] L X) r = algebraMap K[X] L r :=
    fun r => eval₂_algebraMap_X r (IsScalarTower.toAlgHom K K[X] L)
  have h2 : algebraMap K[X] L (p * X ^ n) = algebraMap K[X] L (q.reflect n) := by
    rw [map_mul, map_pow, h, aeval_def, ← hev (q.reflect n)]
    exact key
  have hinj : Function.Injective (algebraMap K[X] L) :=
    IsLocalization.injective L (Submonoid.powers_le.2 X_mem_nonzeroDivisors)
  have h3 := hinj h2
  have hdeg : (p * X ^ n).natDegree ≤ n := h3 ▸ hr
  have hp0 : p.natDegree = 0 := by
    by_cases hp : p = 0
    · simp [hp]
    have hc : (p * X ^ n).coeff (p.natDegree + n) ≠ 0 := by
      rw [coeff_mul_X_pow]; exact mt leadingCoeff_eq_zero.mp hp
    have := le_natDegree_of_ne_zero hc
    omega
  rw [← coeff_zero_eq_eval_zero]
  exact eq_C_of_natDegree_eq_zero hp0

end GlobalTheory

namespace GlobalTheory

theorem chart_map_into_affine_const (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens)
    (hW : IsAffineOpen W) (g₀ g₁ : Sp (Polynomial K) ⟶ Y) (h₀ : ∀ x, g₀ x ∈ W) (h₁ : ∀ x, g₁ x ∈ W)
    (h : spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) :
        Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁) :
    g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  haveI := hW.isOpenImmersion_fromSpec
  have r₀ : Set.range g₀.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₀ x
  have r₁ : Set.range g₁.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₁ x
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₀ r₀)
  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₁ r₁)
  have e₀ : Spec.map φ₀ ≫ hW.fromSpec = g₀ := by rw [hφ₀]; exact IsOpenImmersion.lift_fac _ _ _
  have e₁ : Spec.map φ₁ ≫ hW.fromSpec = g₁ := by rw [hφ₁]; exact IsOpenImmersion.lift_fac _ _ _
  rw [← e₀, ← e₁] at h
  simp only [spMap, ← Category.assoc, ← Spec.map_comp, cancel_mono] at h
  rw [Spec.map_inj] at h
  have key : ∀ a, φ₀ a = Polynomial.C ((φ₀ a).eval 0) := fun a =>
    poly_eq_C_of_eq_aeval_invSelf (φ₀ a) (φ₁ a) (congrArg (fun f => f.hom a) h)
  rw [← e₀]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact key a

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartMapIntoAffineConstStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq : ∀ (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens), IsAffineOpen W → ∀ (g₀ g₁ : Sp (Polynomial K) ⟶ Y), (∀ x, g₀ x ∈ W) → (∀ x, g₁ x ∈ W) → spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) : Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁ → g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  first | exact @GlobalTheory.chart_map_into_affine_const | exact GlobalTheory.chart_map_into_affine_const | (intros; apply GlobalTheory.chart_map_into_affine_const <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineChartFamiliesAgreeOnOverlapStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LineConst

theorem _root_.GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap : ∀ {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f₀ f₁ : Sp (Polynomial k) ⟶ B.left) (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k))) (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k))), spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ (R : Type) [CommRing R] [Algebra k R] (u v : R), u * v = 1 → spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ famMap B f₀ h0 R u = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ famMap B f₁ h1 R v := by
  first | exact @GlobalTheory.LineConst.famMap_loc_eq | exact GlobalTheory.LineConst.famMap_loc_eq | (intros; apply GlobalTheory.LineConst.famMap_loc_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineToAbelianVarietyConst

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineConst
open Polynomial

theorem projLine_map_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (f₀ f₁ : Sp (Polynomial k) ⟶ B.left), f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)) → spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f₀ = spMap b.toRingHom ≫ f₀ := by
  intro k _ _ B _ hB f₀ f₁ h0 h1 h01 a b
  have := hB.proper
  haveI hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let pt : Sp k := IsLocalRing.closedPoint k
  let e : B.left := (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left pt
  obtain ⟨_, ⟨W, hW, rfl⟩, heW, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ e) isOpen_univ
  let L := Localization.Away (X : Polynomial k)
  let t : L := algebraMap (Polynomial k) L X
  let ti : L := IsLocalization.Away.invSelf (X : Polynomial k)
  have hti : t * ti = 1 := IsLocalization.Away.mul_invSelf (X : Polynomial k)
  let g₀ := famMap B f₀ h0 L t
  let g₁ := famMap B f₁ h1 L ti
  have hc := GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 L t ti hti
  let V : Set (Sp L) := {τ | ∀ x : Sp (Polynomial L), spMap (algebraMap L (Polynomial L)) x = τ → g₀ x ∈ W ∧ g₁ x ∈ W}
  have hV : IsOpen V := GlobalTheory.T.isOpen_setOf_fibre_charts_mem L _ g₀ g₁ hc W

  have hfib : ∀ (χ : L →ₐ[k] k) (x' : Sp (Polynomial k)),
      spMap (algebraMap L (Polynomial L)) (spMap (Polynomial.mapRingHom (χ : L →+* k)) x') = spMap χ.toRingHom pt := by
    intro χ x'
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.mapRingHom (χ : L →+* k)).comp (algebraMap L (Polynomial L)) =
        (algebraMap k (Polynomial k)).comp (χ : L →+* k) := by
      ext z; simp [Polynomial.algebraMap_apply]
    rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Scheme.Hom.comp_apply]
    congr 1
    exact hsub.elim _ _
  have hW₀ : ∀ χ : L →ₐ[k] k, spMap χ.toRingHom pt ∈ V →
      (∀ x', famMap B f₀ h0 k (χ t) x' ∈ W) ∧ (∀ x', famMap B f₁ h1 k (χ ti) x' ∈ W) := by
    intro χ hχ
    constructor
    · intro x'
      rw [← famMap_base B f₀ h0 χ t, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).1
    · intro x'
      rw [← famMap_base B f₁ h1 χ ti, Scheme.Hom.comp_apply]
      exact (hχ _ (hfib χ x')).2
  have hinW : ∀ R : Type, ∀ _ : CommRing R, ∀ _ : Algebra k R, ∀ (f : Sp (Polynomial k) ⟶ B.left)
      (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (x : Sp (Polynomial R)), famMap B f hf R 1 x ∈ W := by
    intro R _ _ f hf x
    rw [famMap_one, Scheme.Hom.comp_apply]
    have hx : (spMap (algebraMap k (Polynomial R))) x = pt := hsub.elim _ _
    rw [hx]
    exact heW

  let χ₁ : L →ₐ[k] k := IsLocalization.liftAlgHom (M := Submonoid.powers (X : Polynomial k))
    (f := Polynomial.aeval (1 : k)) (by
      rintro ⟨_, n, rfl⟩
      simp)
  have hχ₁t : χ₁ t = 1 := by simp [χ₁, t]
  have hχ₁ti : χ₁ ti = 1 := by
    have := congrArg χ₁ hti
    rw [map_mul, hχ₁t, _root_.one_mul, map_one] at this
    exact this
  have h1V : spMap χ₁.toRingHom pt ∈ V := by
    intro x hx
    obtain ⟨x', rfl⟩ := GlobalTheory.T.mem_range_spMap_mapRingHom_of_fibre_closedPoint L k χ₁.toRingHom
      (fun z => ⟨algebraMap k L z, by simp⟩) x hx
    constructor
    · have := famMap_base B f₀ h0 χ₁ t
      rw [hχ₁t] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₀ h0 x'
    · have := famMap_base B f₁ h1 χ₁ ti
      rw [hχ₁ti] at this
      rw [← Scheme.Hom.comp_apply]
      erw [this]
      exact hinW k _ _ f₁ h1 x'
  have hF := GlobalTheory.T.finite_compl_punctured_line_open k V hV χ₁ h1V
  set F := {c : k | c ≠ 0 ∧ ∀ χ : L →ₐ[k] k, χ (algebraMap (Polynomial k) _ X) = c → spMap χ.toRingHom pt ∉ V}

  have hscale : ∀ c : k, c ≠ 0 → c ∉ F → ∀ a : k,
      spMap (Polynomial.evalRingHom (c * a)) ≫ f₀ = spMap (Polynomial.evalRingHom a) ≫ f₀ := by
    intro c hc0 hcF
    simp only [F, Set.mem_setOf_eq, not_and, not_forall, not_not] at hcF
    obtain ⟨χ, hχt, hχV⟩ := hcF hc0
    obtain ⟨hA, hB'⟩ := hW₀ χ hχV
    have hu : χ t * χ ti = 1 := by rw [← map_mul, hti, map_one]
    have hcmp := GlobalTheory.T.projectiveLine_chart_families_agree_on_overlap B f₀ f₁ h0 h1 h01 k (χ t) (χ ti) hu
    have key := GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq k B.left W hW _ _ hA hB' hcmp
    have := scale_inv_of_famMap B f₀ h0 (χ t) key
    simpa [t, hχt] using this
  have hunit : ∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f₀ = spMap (Polynomial.evalRingHom 1) ≫ f₀ := by
    intro c hc
    have hfin : ((F ∪ {0}) ∪ (fun d => c / d) '' F).Finite :=
      (hF.union (Set.finite_singleton 0)).union (hF.image _)
    obtain ⟨d, hd⟩ := hfin.infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_image, not_or, not_exists,
      not_and] at hd
    obtain ⟨⟨hdF, hd0⟩, hd'⟩ := hd
    have hcd0 : c / d ≠ 0 := div_ne_zero hc hd0
    have hcdF : c / d ∉ F := fun h => hd' (c / d) h (by field_simp)
    have e1 := hscale d hd0 hdF (c / d * 1)
    have e2 := hscale (c / d) hcd0 hcdF 1
    rw [_root_.mul_one] at e1 e2
    rw [show d * (c / d) = c by field_simp] at e1
    rw [e1, e2]
  exact GlobalTheory.T.affineLine_morphism_constant_of_const_on_nonzero k B.left B.hom f₀ h0 hunit a b

end GlobalTheory.LineConst
end
end

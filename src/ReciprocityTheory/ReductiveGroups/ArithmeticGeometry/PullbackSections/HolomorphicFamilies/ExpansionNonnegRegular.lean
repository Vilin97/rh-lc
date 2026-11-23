module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
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
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenGeneric
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenDiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenLevel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenTerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenThick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RegUnifCut

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

def RegularSectionNonneg : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V)))
      [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
      (U : Unif (maximalIdeal V) D A G) (k : ℕ), k = 1 →
      ∀ (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (s : U.SecK k),
        GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s
          (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) 1 →
      ∀ E : Fam D.toPre (FractionRing V) k, U.Expands k s E → NuGe D Q (FractionRing V) vK k E 0

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenIff

section

@[expose] public section

set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm SectionScalarValuation

section Scale

end Scale

section Integral

open IsLocalRing

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem integral_exp [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1) :
    ∃ (F : Fam D.toPre (FractionRing R) 1) (g' : ∀ α, D.toPre.SecB 1 α), U.Expands 1 (secK U.toUnifPre s) F ∧
      (∀ e, U.ExpandsAt e 1 s g') ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α)
        (DegPre.famε 1) (F.s α) (D.toPre.famφB α) (DegPre.famε 1) (g' α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  have := flat_G U.toUnifPre
  have := flat_B (D := D)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hIϖ : I = Ideal.span {ϖ} := by
    rw [hI, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  obtain ⟨F, hF, -⟩ := (U.expand 1 le_rfl).1 (secK U.toUnifPre s)
  have hF0 := hF
  obtain ⟨r, hr0, σ, f, hσ, hfK, hexp⟩ := hF
  have hσr := sec_eq_of_secScal U.toUnifPre s σ (secK U.toUnifPre s) r (secK_rel U.toUnifPre s) hσ
  obtain ⟨n, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  let τ : H0 U.LG.L 1 := SecOps.secScale (scal G.hom (u : R)) s
  have hστ : ∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j := fun j => by
    rw [hσr, hru]
    show _ = _ * (toW G.hom _ (u : R) * s.f j)
    rw [map_mul, mul_comm (toW G.hom _ (u : R)), _root_.mul_assoc]
  obtain ⟨g, hfg, hexpg⟩ := expand_div_pow U.toUnifPre ReciprocityTheory.ChartRestriction.G.Out.WeightPf.weightIndep hϖ.ne_zero hIϖ n σ τ hστ f hexp
  let g' : ∀ α, D.toPre.SecB 1 α := fun α => SecOps.secScale (scal D.toPre.P.A.hom ((u⁻¹ : Rˣ) : R)) (g α)
  have hexp' : ∀ e, U.ExpandsAt e 1 s g' := fun e =>
    expandsAt_scale U.toUnifPre ((u⁻¹ : Rˣ) : R) τ s (fun j => by
      show _ = _ * (toW G.hom _ (u : R) * s.f j)
      rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]) g g' (fun α j => rfl) e (hexpg e)
  have hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α)
      (D.toPre.famφB α) (DegPre.famε 1) (g' α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
    intro α j₁ j₂ hc
    have e := hfK α j₁ j₂ hc
    have hf' : (f α).f j₂ = toW D.toPre.P.A.hom _ r * (g' α).f j₂ := by
      rw [hfg α j₂]
      show _ = _ * (toW _ _ ((u⁻¹ : Rˣ) : R) * (g α).f j₂)
      rw [← _root_.mul_assoc, ← map_mul, hru, mul_comm (u : R), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    have hBF : (DegPre.BF D.toPre (FractionRing R)).hom =
        (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
      simp [DegPre.BF, TF]
    have hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom :=
      Over.w _
    erw [hf', map_mul, app_toW, map_mul, toW_res, resTop_scal, toW_congr hw] at e
    have hu := isUnit_toW_of_K (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R))
      (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂) hr0
    rw [← toW_congr hBF] at hu
    have e2 := hu.mul_left_cancel e
    have h1 : resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂)
        (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 := map_one _
    rw [h1, _root_.one_mul]
    exact e2
  exact ⟨F, g', hF0, hexp', hgF⟩

end Integral

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpansionNonnegRegular

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

private lemma coh_lemma {X Y : Scheme} (L : LB X) (φ : Fin 1 ⊕ Fin 1 → (Y ⟶ X))
    (j : Fin 1 → L.ι) : LB.Coh L φ (Sum.elim j j) := by
  intro k₁ k₂ _
  rcases k₁ with a | a <;> rcases k₂ with b | b <;> exact congrArg j (Subsingleton.elim a b)

private lemma res_inj_lemma_2 {X : Scheme} {W V : X.Opens} (h : W ≤ V) {a b : Γ(X, V)}
    {c : Γ(X, W)} (hc : c = 1)
    (hab : c * (X.presheaf.map (homOfLE h).op).hom a = c * (X.presheaf.map (homOfLE h).op).hom b)
    (h' : V ≤ W) : a = b := by
  subst hc
  rw [_root_.one_mul, _root_.one_mul] at hab
  have hWV : W = V := le_antisymm h h'
  subst hWV
  have e : homOfLE h = 𝟙 W := Subsingleton.elim _ _
  rw [e] at hab
  simpa using hab

theorem expansion_nonneg_regular : RegularSectionNonneg := by
  unfold RegularSectionNonneg
  intro V _ _ _ ϖ hϖ D Q hQ vK hvK A G _ _ _ _ _ U k hk σ s hs E hE
  subst hk
  obtain ⟨F, g', hF, -, hFg⟩ := TG.integral_exp (U := U) rfl σ

  have hsK : s = TG.secK U.toUnifPre σ := by
    apply SecOps.sec_ext
    intro j
    have h1 := hs j j (coh_lemma _ _ j)
    have h2 := TG.secK_rel U.toUnifPre σ j j (coh_lemma _ _ j)
    have h3 := h1.symm.trans h2
    refine res_inj_lemma_2 _ (by exact _root_.map_one _) h3 ?_
    refine le_inf le_rfl ?_
    first
      | exact le_rfl
      | (simp only [Category.comp_id]; exact le_rfl)
      | exact fun x hx => hx
      | (intro x hx; simpa [LB.wchart] using hx)
  subst hsK

  have hEF : E = F := ((U.expand 1 le_rfl).1 _).unique hE hF
  rw [hEF]
  refine (n1a V ϖ hϖ D Q hQ (FractionRing V) vK hvK 1 le_rfl {0}
    (fun χ => ⟨0, Finset.mem_singleton_self 0, χ, by simp⟩) F 0).2 ?_
  intro α hα
  rw [Finset.mem_singleton] at hα
  subst hα
  rw [Q_zero hϖ (hQ := hQ)]
  unfold VGe
  refine ⟨1, fun _ => 1, fun _ => g' 0, fun _ => F.s 0, fun _ => hFg 0, fun _ => ?_, fun j => ?_⟩
  · first
      | simp
      | (rw [AddValuation.map_one]; simp)
  · first
      | simp [DegPre.constBF]
      | (simp only [DegPre.constBF, Fin.sum_univ_one, _root_.map_one, _root_.one_mul])

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
end

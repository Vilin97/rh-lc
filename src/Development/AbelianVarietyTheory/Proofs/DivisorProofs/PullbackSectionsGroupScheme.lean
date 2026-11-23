module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoLBCover
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetE
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnGerm

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

section Pt

variable {K : Type} [Field K] {ι : Type} {m : ℕ}

end Pt

section PullSec

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A)
  (hh : h ≫ snd T A = snd T' A)

def anPullF (s : LB.Sec (LPow A L a T)) (j : Fin 1 → L.ι) : Γ((T' ⊗ A).left, (LPow A L a T').U j) :=
  ((T' ⊗ A).left.presheaf.map (homOfLE (chart_le_res A L h hh a j)).op).hom ((h.left.app _).hom (s.f j))

def pullSecLP (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') where
  f := anPullF A L a h hh s
  compat i j := fn_ext fun y hy => by
    have hi : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) i := chart_le_res A L h hh a i hy.1
    have hj : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) j := chart_le_res A L h hh a j hy.2
    have v : ∀ j', y ∈ (LPow A L a T').U j' → gs (𝟙 _) y _ (anPullF A L a h hh s j') =
        gs (𝟙 _ ≫ h.left) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j') (s.f j') := fun j' hj' =>
      (gs_res _ y _ hj' _).trans (gs_pull _ h.left y _ (chart_le_res A L h hh a j' hj') _)
    refine ((gs_res (𝟙 _) y _ hy _).trans ((v i hy.1).trans (sec_trans s (𝟙 _ ≫ h.left) y hi hj))).trans ?_
    refine Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm
    refine congrArg₂ (· * ·) ?_ ((v j hy.2).symm.trans (gs_res (𝟙 _) y _ hy _).symm)
    refine Eq.trans ?_ (gs_unit (𝟙 _) y _ hy _).symm
    refine congrArg Units.val (Eq.trans ?_
      (gm_linComb L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) (𝟙 _) y i j hy.1 hy.2).symm)
    simp only [trF, Category.assoc, ← Over.comp_left, hh]

theorem isPullSec_pullSecLP (s : LB.Sec (LPow A L a T)) : IsPullSec A L a h hh s (pullSecLP A L a h hh s) := fun _ => rfl

end PullSec

section Fam

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (L : LB G.left) {x0 : Sp ℂ ⟶ X} {g : ℕ}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (hol : IsHolFam e) (he : ∀ z, e z ≫ G.hom = x0)

def jB (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 :=
  Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m))) rfl

def xJ (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ G :=
  Over.homMk (jetPt e hol m) (jetPt_over e hol G.hom x0 he m)

def ePt (z : Fin g → ℂ) : Over.mk x0 ⟶ G := Over.homMk (e z) (he z)

def lftJ (z : Fin g → ℂ) : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left := (ptSecT G (ePt e he z)).left


end Fam

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupScheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixIndep

theorem eq_zero_of_locally {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ (X.presheaf.map (homOfLE hW).op).hom s = 0) :
    s = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, h0⟩ := h x hx
  have e1 := X.presheaf.germ_res_apply (homOfLE hW) x hxW s
  change (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom 0
  rw [← e1, h0, map_zero, map_zero]

theorem appLE_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f₁ ⁻¹ᵁ U) (a : Γ(Y, U)) :
    (f₁.appLE U V e).hom a = (f₂.appLE U V (h ▸ e)).hom a := by
  subst h; rfl

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V W : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V)
    (a : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_appLE {X Y Z : Scheme.{0}} (g : X ⟶ Y) (f : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : W ≤ g ⁻¹ᵁ V) (a : Γ(Z, U)) :
    (g.appLE V W e₂).hom ((f.appLE U V e₁).hom a) =
      ((g ≫ f).appLE U W (fun _ hx => e₁ (e₂ hx))).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.HomFixIndep


open GlobalTheory.HomFixIndep in
theorem GlobalTheory.HomFixIndep.pulled_basis_indep : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  intro Rg _ A _ L k mA bA hB R _ t A' _ φA' ψA hT hψ d hloc
  let t'' : Spec (CommRingCat.of R) ⟶ (topS Rg).left :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι t (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial)
  have ht'' : (baseAt t'').hom = t := by simp [t'', baseAt, topS, overRes, baseOver]
  set T := baseAt t'' with hTdef
  have hw : (snd T A).left ≫ A.hom = (fst T A).left ≫ t := by
    rw [← ht'', Over.w (snd T A), Over.w (fst T A)]
  let g : (T ⊗ A).left ⟶ A'.left := hT.1.lift (snd T A).left (fst T A).left hw
  have hg1 : g ≫ φA' = (snd T A).left := hT.1.lift_fst _ _ _
  have hg2 : g ≫ A'.hom = (fst T A).left := hT.1.lift_snd _ _ _
  have hgψ : g ≫ ψA = (homAt t'' ▷ A).left := by
    apply psi_unique
    rw [Category.assoc, hψ, hg1, ← Over.comp_left, whiskerRight_snd]
  let b' : Fin mA → LB.Sec (LPow A L (k : ℤ) T) := fun i =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLP A L (k : ℤ) (homAt t'' ▷ A) (whiskerRight_snd (homAt t'') A) (bA i)
  obtain ⟨hli, -⟩ := hB R t'' b' (fun i => ReciprocityTheory.ChartRestriction.G.PullbackSections.isPullSec_pullSecLP A L (k : ℤ) _ _ (bA i))
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  refine hli d ?_ i
  apply Subtype.ext
  funext j
  have hD : (LPow A L (k : ℤ) T).U j ≤ g ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j := by
    intro y hy
    have e : g ≫ ψA ≫ (snd (topS Rg) A).left = (snd T A).left := by
      rw [← Category.assoc, hgψ, ← Over.comp_left, whiskerRight_snd]
    have h1 : (g ≫ ψA ≫ (snd (topS Rg) A).left).base y ∈ (L.U (j 0) : Set A.left) := by
      rw [e]; exact Set.mem_iInter.1 hy 0
    exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1
  have hF : (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) = 0 := by
    refine eq_zero_of_locally _ fun x hx => ?_
    obtain ⟨W, hW, hxW, h0⟩ := hloc j x hx
    refine ⟨W, hW, hxW, ?_⟩

    rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h0
    rw [map_mul]
    exact congrArg₂ (· * ·) (res_appLE _ _ _ _ _ _ _) (res_appLE _ _ _ _ _ _ _)
  calc (∑ i, d i • SecM.ofSec A (b' i)).val j
      = ∑ i, ((fst T A).left.appLE ⊤ ((LPow A L (k : ℤ) T).U j) (by simp)).hom (d i) *
          ((homAt t'' ▷ A).left.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
            ((LPow A L (k : ℤ) T).U j) (chart_le_res A L _ (whiskerRight_snd (homAt t'') A) _ j)).hom ((bA i).f j) := by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
    _ = (g.appLE _ _ hD).hom (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) := by

        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        exact congrArg₂ (· * ·) (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hg2 _ _ _ _)).symm)
          (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hgψ _ _ _ _)).symm)
    _ = _ := by rw [hF, map_zero]; rfl
end
end
end

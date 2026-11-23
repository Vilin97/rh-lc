module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoLBCover
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetE
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOne

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUnit

theorem ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  intro Rg _ A B _ _ L M k eA eB hA hL hM R _ t A' B' _ _ φA' φB' Φ' ψA ψB α α₂ v hT hψA hψB hv hα hα₂
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hT.1
  refine Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.unit_eq_one_of_eSec GlobalTheory.globalFns_holds A' hA' v ?_
  show (zeroPt A').appTop.hom v.val = 1
  let W : ((Fin 1 → M.ι) × (Fin 1 → L.ι)) → (Sp R).Opens := fun p =>
    (zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
      t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
      t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)
  have hloc : ∀ p, ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom
      ((zeroPt A').appTop.hom v.val) = 1 := by
    intro p
    have h1 := hα p
    have h2 := hα₂ p
    rw [hv p, Units.val_mul, map_mul] at h1
    have hres : (Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
        (inf_le_left.trans inf_le_left)).hom
          ((res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ) : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)) =
        ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom ((zeroPt A').appTop.hom v.val) := by
      show (A'.left.presheaf.map (homOfLE (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤)).op ≫
        Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
          (inf_le_left.trans inf_le_left)).hom v.val = _
      rw [Scheme.Hom.map_appLE]
      rfl
    rw [hres] at h1
    have key := h1.trans h2.symm
    rw [_root_.mul_assoc] at key
    exact (IsUnit.mul_left_inj (IsUnit.mul ((α₂.s p).isUnit.map _) (((eA.s _).isUnit.map _).pow k))).1
      (key.trans (_root_.one_mul _).symm)
  have hcov : (⊤ : (Sp R).Opens) ≤ iSup W := by
    rintro x -
    have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
    obtain ⟨iL, hiL⟩ := hc L hL ((eSec A) (t x))
    obtain ⟨iM, hiM⟩ := hc M hM ((eSec B) (t x))
    haveI := hT.2.2.1
    have eA' : zeroPt A' ≫ ψA ≫ (snd (topS Rg) A).left = t ≫ eSec A := by
      rw [hψA]; exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.1
    have eB' : zeroPt A' ≫ (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = t ≫ eSec B := by
      have h0 : zeroPt A' ≫ Φ'.left = zeroPt B' := congrArg Over.Hom.left (IsMonHom.one_hom Φ')
      rw [Category.assoc, hψB, ← Category.assoc, h0]
      exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.2.1
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => iM, fun _ => iL), ?_⟩
    refine ⟨⟨⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩, Set.mem_iInter.2 fun _ => hiL⟩,
      Set.mem_iInter.2 fun _ => hiM⟩
    · show ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (zeroPt A' x) ∈ M.U iM
      rw [← Scheme.Hom.comp_apply, eB', Scheme.Hom.comp_apply]
      exact hiM
    · show (ψA ≫ (snd (topS Rg) A).left) (zeroPt A' x) ∈ L.U iL
      rw [← Scheme.Hom.comp_apply, eA', Scheme.Hom.comp_apply]
      exact hiL
  exact TopCat.Sheaf.eq_of_locally_eq' (Sp R).sheaf W ⊤ (fun p => homOfLE le_top) hcov _ 1
    (fun p => (hloc p).trans (map_one ((Sp R).presheaf.map (homOfLE le_top : W p ⟶ ⊤).op).hom).symm)

end GlobalTheory.HomFixUnit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

theorem _root_.GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  first | (exact @GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (exact GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (intros; apply GlobalTheory.HomFixUnit.ratio_unit_eq_one  <;> assumption)
end
end

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

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupSchemeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

theorem _root_.GlobalTheory.T.pullback_sections_group_scheme : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  first | (exact @GlobalTheory.HomFixIndep.pulled_basis_indep) | (exact GlobalTheory.HomFixIndep.pulled_basis_indep) | (intros; apply GlobalTheory.HomFixIndep.pulled_basis_indep  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismMatrixUniqueFixedPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUniq

theorem mat_unique : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c c' : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c' → c = c' := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' c c' hT h₁ h₂
  obtain ⟨hAab, -, hL, hM, -, -, -, -, -, hbA, -⟩ := hH
  obtain ⟨ψA, ψB, α, hψA, hψB, hα, hrig, hmat⟩ := h₁
  obtain ⟨ψA₂, ψB₂, α₂, hψA₂, hψB₂, hα₂, hrig₂, hmat₂⟩ := h₂
  obtain rfl : ψA₂ = ψA := psi_unique _ _ (hψA₂.trans hψA.symm)
  obtain rfl : ψB₂ = ψB := psi_unique _ _ (hψB₂.trans hψB.symm)
  obtain ⟨v, hv⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.exists_ratio_gen
    (isoLB_cover (L := L) (M := M) hL hM k Φ' ψA₂ ψB₂) hα hα₂
  have v1 : v = 1 := GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one Rg A B L M k eA eB hAab hL hM R t A' B' φA' φB' Φ' ψA₂ ψB₂ α α₂ v hT hψA hψB hv hrig hrig₂
  have hαe : ∀ p, α.s p = α₂.s p := fun p => by rw [hv p, v1, map_one, _root_.one_mul]
  funext i j
  have hd := GlobalTheory.T.pullback_sections_group_scheme Rg A L k mA bA hbA R t A' φA' ψA₂ hT.1 hψA₂ (fun i => c i j - c' i j) (fun jL x hx => by
    obtain ⟨iM, hiM⟩ : ∃ iM, ((((Φ'.left ≫ ψB₂) ≫ (snd (topS Rg) B).left)).base x) ∈ M.U iM :=
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hM.cover]; trivial)
    refine ⟨(isoLB (L := L) (M := M) k Φ' ψA₂ ψB₂).U (fun _ => iM, jL), inf_le_right,
      ⟨Set.mem_iInter.2 fun _ => hiM, hx⟩, ?_⟩
    have e := (hmat j (fun _ => iM, jL)).symm.trans (hmat₂ j (fun _ => iM, jL))
    have e1 := congrArg Units.val (hαe (fun _ => iM, jL))
    erw [e1] at e
    have e2 := (α₂.s (fun _ => iM, jL)).isUnit.mul_left_cancel e
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 e2)
  exact sub_eq_zero.1 (congrFun hd i)

end GlobalTheory.HomFixUniq
end
end
end

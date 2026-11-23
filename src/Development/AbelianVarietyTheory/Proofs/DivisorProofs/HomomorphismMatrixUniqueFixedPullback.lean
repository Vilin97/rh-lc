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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupSchemeStatement
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

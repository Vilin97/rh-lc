module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LbIsoLinCombPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionBaseChangeAlgebraMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecBC

theorem sqDec_baseChange : ∀ (k R S : Type) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) (A₀ : Over (Sp k)) [GrpObj A₀] (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) → SqDec ((Over.pullback (spMap (algebraMap k S))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) := by
  intro k R S _ _ _ _ _ ρ A₀ _ L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  set bc := GlobalTheory.Spread.bcMap A₀.hom ρ with hbc
  have hg' : ∀ i, ∃ g : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀,
      IsMonHom g ∧ g.left ≫ bc = bc ≫ (β i).left := by
    intro i
    haveI := hβ i
    obtain ⟨g, hg, e⟩ := GlobalTheory.HomDescent.exists_specialise (β i) ρ
    refine ⟨g, hg, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_fst, e, Category.assoc]
    · have w₁ := Over.w g
      have w₂ := Over.w (β i)
      simp only [Over.pullback_obj_hom] at w₁ w₂
      rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_snd, ← Category.assoc, w₁, Category.assoc, w₂, GlobalTheory.Spread.bcMap_snd]
  choose g hgm hgc using hg'
  refine ⟨N, a₀, r, a, g, hN, ha₀, hgm, ?_⟩
  set fR := pullback.fst A₀.hom (spMap (algebraMap k R)) with hfR
  set fS := pullback.fst A₀.hom (spMap (algebraMap k S)) with hfS
  have efS : fS = bc ≫ fR := (GlobalTheory.Spread.bcMap_fst A₀.hom ρ).symm
  have pullIso : ∀ {X Y : Scheme.{0}} {P Q : LB X}, LBIso P Q → ∀ f : Y ⟶ X, LBIso (P.pull f) (Q.pull f) :=
    fun h f => h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl)
  have i1 := lbIso_lbPow_pull hL fS N
  have i2 := GlobalTheory.Spread.lbIso_pull_pull (isLB_lbPow hL N) bc efS
  have i3 := pullIso (lbIso_lbPow_pull hL fR N).symm bc
  have i4 := pullIso H bc
  have hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (g i).left) ≫ bc = bc ≫ (o.elim (𝟙 _) fun i => (β i).left) := by
    intro o
    cases o with
    | none => simp
    | some i => exact hgc i
  have i5 := (GlobalTheory.SymExtend.lbIso_linComb_pull (pull_isLB hM fR) bc (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (g i).left)
    (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) bc hc).symm
  have i6 : LBIso (LB.LinComb ((M.pull fR).pull bc) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)))
      (LB.LinComb (M.pull fS) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ))) := by
    obtain ⟨w, hw⟩ := (GlobalTheory.Spread.lbIso_pull_pull hM bc efS).symm
    exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩
  have j1 := i1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _)
    (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _) i2
  have j2 := j1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _)
    (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _) i3
  have j3 := j2.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
    (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _) i4
  have j4 := j3.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _)
    (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _) i5
  exact j4.trans (isLB_lbPow (pull_isLB hL _) N) (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _)
    (LB.isLB_linComb (pull_isLB hM _) _ _) i6

end GlobalTheory.SqDecBC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionBaseChangeAlgebraMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.squareDecomposition_baseChange_algebraMap : ∀ (k R S : Type) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) (A₀ : Over (Sp k)) [GrpObj A₀] (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) → SqDec ((Over.pullback (spMap (algebraMap k S))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) := by
  first | exact @GlobalTheory.SqDecBC.sqDec_baseChange | exact GlobalTheory.SqDecBC.sqDec_baseChange | (intros; apply GlobalTheory.SqDecBC.sqDec_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFinitelyGenerated

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecSpread

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [Field k] (A₀ : Over (Sp k))

theorem lbIso_lbPow_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {L : LB A₀.left} (hL : L.IsLB) (N : ℕ) :
    LBIso (lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) N)
      ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) N).pull (bcMap A₀.hom ρ)) := by
  have h₁ : LBIso (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hL _ (bcMap_fst A₀.hom ρ).symm
  have hR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow (pull_isLB hR _) N)
    (pull_isLB (isLB_lbPow hR N) _) (lbIso_lbPow h₁ N) (lbIso_lbPow_pull hR _ N)

theorem lbIso_linComb_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {M : LB A₀.left} (hM : M.IsLB) {K : Type} [Fintype K]
    (φS : K → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))))
    (φR : K → (pullback A₀.hom (spMap (algebraMap k R)) ⟶ pullback A₀.hom (spMap (algebraMap k R))))
    (ε : K → ℤ) (hφ : ∀ o, φS o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ φR o) :
    LBIso (LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) φS ε)
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) φR ε).pull (bcMap A₀.hom ρ)) := by
  have hR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have h₁ : LBIso (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hM _ (bcMap_fst A₀.hom ρ).symm
  exact LBIso.trans (LB.isLB_linComb (pull_isLB hM _) _ _) (LB.isLB_linComb (pull_isLB hR _) _ _)
    (pull_isLB (LB.isLB_linComb hR _ _) _) (PelPrim.lbIso_linComb h₁ φS ε)
    (SymExtend.lbIso_linComb_pull hR (bcMap A₀.hom ρ) φS φR ε (bcMap A₀.hom ρ) hφ)

theorem comm_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    (f : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)
    (g : (Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀)
    (h : bcMap A₀.hom ρ ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ g.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, Category.assoc, h]
  · have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
    have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
    rw [Category.assoc, bcMap_snd, ← Category.assoc, hf, Category.assoc, hg, bcMap_snd]

def fam {S : Type} [CommRing S] [Algebra k S] {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)) :
    Option (Fin r) → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))) :=
  fun o => o.elim (𝟙 _) fun i => (β i).left

theorem fam_comm {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀))
    (gam : Fin r → ((Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀))
    (h : ∀ i, bcMap A₀.hom ρ ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _) (o : Option (Fin r)) :
    fam A₀ β o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ fam A₀ gam o := by
  cases o with
  | none => simp [fam]
  | some i => exact comm_bc A₀ ρ (β i) (gam i) (h i)

end GlobalTheory.SqDecSpread


open GlobalTheory.Spread GlobalTheory.HomDescent GlobalTheory.SqDecSpread in
theorem GlobalTheory.SqDecSpread.sqDec_fg : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A₀ : Over (Sp k)) [GrpObj A₀],
    IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB →
    SqDec ((Over.pullback (spMap (algebraMap k Ω))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω))))
      (M.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) →
    ∃ R : Subalgebra k Ω, R.FG ∧ SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀)
      (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) := by
  intro k Ω _ _ _ A₀ _ hA L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  have := hA.proper
  have := hA.smooth
  let ε : Option (Fin r) → ℤ := fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)
  choose Ri g hRi hg hgeq using fun i => haveI := hβ i; exists_fg_isMonHom (A := A₀) (A' := A₀) (β i)
  let R₁ : Subalgebra k Ω := ⨆ i, Ri i
  have hR₁ : R₁.FG := fg_iSup hRi
  choose gam hgam hgameq using fun i => haveI := hg i; exists_specialise (g i) (Subalgebra.inclusion (le_iSup Ri i))
  have key₁ : ∀ i, bcMap A₀.hom R₁.val ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _ := by
    intro i
    rw [hgameq i, ← Category.assoc, bcMap_comp_of_eq A₀.hom (Subalgebra.inclusion (le_iSup Ri i)) R₁.val (Ri i).val
      (fun _ => rfl), hgeq i]
  have hL₁ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hM₁ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hLΩ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have hMΩ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have H₁ : LBIso ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) N).pull (baseChangeMap A₀.hom R₁.val))
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) (fam A₀ gam) ε).pull
        (baseChangeMap A₀.hom R₁.val)) :=
    LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (isLB_lbPow hLΩ N) (pull_isLB (LB.isLB_linComb hM₁ _ _) _)
      (lbIso_lbPow_bc A₀ R₁.val hL N).symm
      (LBIso.trans (isLB_lbPow hLΩ N) (LB.isLB_linComb hMΩ _ _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) H
        (lbIso_linComb_bc A₀ R₁.val hM (fam A₀ β) (fam A₀ gam) ε (fam_comm A₀ R₁.val β gam key₁)))
  obtain ⟨R, hR, hRfg, H₂⟩ := exists_fg_lbIso A₀.hom hR₁ _ _ (isLB_lbPow hL₁ N) (LB.isLB_linComb hM₁ _ _) H₁
  choose δ hδ hδeq using fun i => haveI := hgam i; exists_specialise (gam i) (Subalgebra.inclusion hR)
  have hLR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have hMR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  refine ⟨R, hRfg, N, a₀, r, a, δ, hN, ha₀, hδ, ?_⟩
  exact LBIso.trans (isLB_lbPow hLR N) (pull_isLB (isLB_lbPow hL₁ N) _) (LB.isLB_linComb hMR _ _)
    (lbIso_lbPow_bc A₀ (Subalgebra.inclusion hR) hL N)
    (LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) (LB.isLB_linComb hMR _ _) H₂
      (lbIso_linComb_bc A₀ (Subalgebra.inclusion hR) hM (fam A₀ δ) (fam A₀ gam) ε
        (fam_comm A₀ (Subalgebra.inclusion hR) δ gam fun i => (hδeq i).symm)).symm)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFinitelyGeneratedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.squareDecomposition_descends_to_finitelyGenerated : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k Ω))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) → ∃ R : Subalgebra k Ω, R.FG ∧ SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) := by
  first | exact @GlobalTheory.SqDecSpread.sqDec_fg | exact GlobalTheory.SqDecSpread.sqDec_fg | (intros; apply GlobalTheory.SqDecSpread.sqDec_fg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFiniteExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecFinite

theorem exists_algHom_finite (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (hR : R.FG) :
    ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), Nonempty (R →ₐ[k] k₁) := by
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType _).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, inferInstance, ⟨Ideal.Quotient.mkₐ k m⟩⟩

theorem main : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) (M.pull (pullback.fst A₀.hom (spMap σ))) → ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), SqDec ((Over.pullback (spMap (algebraMap k k₁))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) := by
  intro k Ω _ _ σ A₀ _ hA L M hL hM h
  letI := σ.toAlgebra
  obtain ⟨R, hR, hRd⟩ := GlobalTheory.T.squareDecomposition_descends_to_finitelyGenerated k Ω A₀ hA L M hL hM h
  obtain ⟨k₁, _, _, _, ⟨ρ⟩⟩ := exists_algHom_finite k Ω R hR
  exact ⟨k₁, inferInstance, inferInstance, inferInstance, GlobalTheory.T.squareDecomposition_baseChange_algebraMap k R k₁ ρ A₀ L M hL hM hRd⟩

end GlobalTheory.SqDecFinite
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFiniteExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.squareDecomposition_descends_to_finiteExtension : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) (M.pull (pullback.fst A₀.hom (spMap σ))) → ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), SqDec ((Over.pullback (spMap (algebraMap k k₁))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) := by
  first | exact @GlobalTheory.SqDecFinite.main | exact GlobalTheory.SqDecFinite.main | (intros; apply GlobalTheory.SqDecFinite.main <;> assumption)
end
end

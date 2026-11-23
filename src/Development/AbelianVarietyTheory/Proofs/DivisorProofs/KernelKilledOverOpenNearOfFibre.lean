module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerKilledOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearChangeEulerProduct
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupKilledNearPointOfFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessOfClosedSubscheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.KernelRepFinite

theorem isClosedImmersion_pullback_map {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} (k : A ⟶ B)
    [IsClosedImmersion k.left] : IsClosedImmersion ((Over.pullback f).map k).left := by
  exact MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f k inferInstance

theorem lbIso_diag {S T : Scheme.{0}} (A : Over S) (B : Over T) (β : B.left ⟶ A.left)
    (β₂ : (G2 B).left ⟶ (G2 A).left) (hs : IsSquare β β₂) {P : LB (G2 A).left} (hP : P.IsLB) :
    LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) := by
  have e₁ : LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) (P.pull ((lift (𝟙 B) (𝟙 B)).left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) _
  have e₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) (P.pull (β ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
  rw [GlobalTheory.DiagAmpleBC.diag_comp A B β β₂ hs] at e₁
  exact LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm

theorem isFinite_restrict : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∀ V₀ : S'.Opens, IsAffineOpen V₀ → Out.RelAmple ((Over.pullback V₀.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)).pull (lift (𝟙 ((Over.pullback V₀.ι).obj G)) (𝟙 ((Over.pullback V₀.ι).obj G))).left) → ∀ (Z : Over S') (i : Z ⟶ G), IsClosedImmersion i.left → (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) (z ≫ i)) → IsFinite (Z.hom ∣_ V₀) := by
  intro S' _ G _ _ P hA hP V₀ hV hRel Z i hi hZ
  haveI : IsNoetherianRing Γ(S', V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV⟩
  let t : Sp Γ(S', V₀) ⟶ V₀.toScheme := hV.isoSpec.inv
  let GV := (Over.pullback V₀.ι).obj G
  let B := (Over.pullback t).obj GV
  have hAV : IsAbelianScheme GV := GlobalTheory.isAbelianScheme_pullback_obj _ G hA
  have hAB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj _ GV hAV
  let PV := P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)
  have hPV : PV.IsLB := pull_isLB hP _
  have h₁ := Pdiv.PullbackComparison.isGrpPullback V₀.ι G
  have h₂ := Pdiv.PullbackComparison.isGrpPullback t GV
  have hRelB : Out.RelAmple B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) :=
    GlobalTheory.DiagAmpleBC.relAmple_diag_pull _ _ GV hAV PV hPV hRel t B (Pdiv.PullbackComparison.pφ t GV)
      (Pdiv.PullbackComparison.pφ₂ t GV) h₂.1 (Pdiv.PullbackComparison.isSquare t GV)
  obtain ⟨ZL, iL, hiL, hfinL, -, hrep⟩ := GlobalTheory.kernelFiniteFlat_holds _ B hAB _
    (pull_isLB (pull_isLB hPV _) _) hRelB
  let ZV := (Over.pullback V₀.ι).obj Z
  let ZB := (Over.pullback t).obj ZV
  let iV : ZV ⟶ GV := (Over.pullback V₀.ι).map i
  let iB : ZB ⟶ B := (Over.pullback t).map iV
  have hmem : GlobalTheory.MemKL B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) iB := by
    refine GlobalTheory.memKL_of_push h₂ (pull_isLB hPV _) (pull_isLB (pull_isLB hPV _) _)
      (lbIso_diag GV B _ _ (Pdiv.PullbackComparison.isSquare t GV) hPV) iB ?_
    refine GlobalTheory.memKL_of_push h₁ (pull_isLB hP _) (pull_isLB hPV _)
      (lbIso_diag G GV _ _ (Pdiv.PullbackComparison.isSquare V₀.ι G) hP) _ ?_
    let zz : Over.mk ((ZB.hom ≫ t) ≫ V₀.ι) ⟶ Z :=
      Over.homMk (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) (by
        show (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ Z.hom = (pullback.snd ZV.hom t ≫ t) ≫ V₀.ι
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        congr 1
        exact pullback.condition)
    have e : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₁.1.w (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₂.1.w iB) = zz ≫ i := by
      apply Over.OverMorphism.ext
      show (iB.left ≫ Pdiv.PullbackComparison.pφ t GV) ≫ Pdiv.PullbackComparison.pφ V₀.ι G =
        (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ i.left
      simp only [Pdiv.PullbackComparison.pφ]
      rw [Pdiv.PullbackComparison.pullback_map_left_fst' t iV, Category.assoc,
        Pdiv.PullbackComparison.pullback_map_left_fst' V₀.ι i, Category.assoc]
    rw [e]
    apply hZ
    rintro _ ⟨y, rfl⟩
    show (((ZB.hom ≫ t) ≫ V₀.ι).base y) ∈ V₀
    exact (Scheme.Opens.range_ι V₀).subset ⟨(ZB.hom ≫ t).base y, rfl⟩
  obtain ⟨z, hz⟩ := (hrep ZB iB).1 hmem
  haveI : IsClosedImmersion iV.left := isClosedImmersion_pullback_map _ i
  haveI : IsClosedImmersion iB.left := isClosedImmersion_pullback_map _ iV
  have hz' : z.left ≫ iL.left = iB.left := congrArg (fun q => q.left) hz
  haveI : IsClosedImmersion (z.left ≫ iL.left) := by rw [hz']; infer_instance
  haveI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left iL.left
  have hZB : IsFinite ZB.hom := by
    rw [← Over.w z]; infer_instance
  have hV' : IsFinite ZV.hom := by
    have ec : ZV.hom = inv (pullback.fst ZV.hom t) ≫ pullback.snd ZV.hom t ≫ t := by
      rw [← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [ec]
    haveI : IsFinite (pullback.snd ZV.hom t) := hZB
    infer_instance
  rw [← (isPullback_morphismRestrict Z.hom V₀).flip.isoPullback_hom_snd]
  haveI : IsFinite (pullback.snd Z.hom V₀.ι) := hV'
  infer_instance

end GlobalTheory.KernelRepFinite
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAmpleClosedImmersion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.relatively_ample_closed_immersion : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∀ V₀ : S'.Opens, IsAffineOpen V₀ → Out.RelAmple ((Over.pullback V₀.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)).pull (lift (𝟙 ((Over.pullback V₀.ι).obj G)) (𝟙 ((Over.pullback V₀.ι).obj G))).left) → ∀ (Z : Over S') (i : Z ⟶ G), IsClosedImmersion i.left → (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) (z ≫ i)) → IsFinite (Z.hom ∣_ V₀) := by
  first | (exact @GlobalTheory.KernelRepFinite.isFinite_restrict) | (exact GlobalTheory.KernelRepFinite.isFinite_restrict) | (intros; apply GlobalTheory.KernelRepFinite.isFinite_restrict  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteKernelNearDiagonalAmple

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem evc_symm {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    {Y : Over S} (a b : Y ⟶ G) : evc hP a b = evc hP b a := by
  have e := congrArg (CechPic.pull (lift b a).left) ((cls_eq_iff hP (pull_isLB hP _)).2 hs)
  rw [cls_pull hP _ (pull_isLB hP _), ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd] at e
  exact e.symm

theorem evc_eq_zero_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) {Y : Over S} (t : Y ⟶ T) (w : Y ⟶ G) :
    evc hP (t ≫ x) w = 0 := by
  have e := congrArg (CechPic.pull (lift w t).left) ((triv_ev_iff hP _ _).1 hx)
  rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem memKL_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    (a₁ : IsAdditive P) (a₂ : IsAdditive (AbDual.swap P)) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) :
    MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) x := by
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hD : (Out.translDiff G (P.pull (lift (𝟙 G) (𝟙 G)).left) x).IsLB := LB.isLB_linComb hL _ _
  have hdiag : ∀ {Y : Over S} (y : Y ⟶ G), CechPic.pull y.left (cls _ hL) = evc hP y y := fun y => by
    rw [cls_pull hP _ hL, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl
  have z : cls _ hD = 0 := by
    have e₁ := pull_translDiff hL x hD (fst T G) (snd T G)
    rw [lift_fst_snd, Over.id_left, pull_id, hdiag, hdiag] at e₁
    rw [e₁, (isAdditive_iff hP).1 a₁, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂,
      (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂, evc_eq_zero_of_triv hP hx, evc_eq_zero_of_triv hP hx,
      evc_symm hP hs (snd T G) (fst T G ≫ x), evc_eq_zero_of_triv hP hx]
    simp
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, z, map_zero]

end GlobalTheory.KernelNear

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

theorem exists_finite_kernel_near : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → ∀ s ∈ W, ∃ (V₀ : S'.Opens) (Z : Over S') (i : Z ⟶ G), s ∈ V₀ ∧ Mono i ∧ IsFinite (Z.hom ∣_ V₀) ∧ (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) ∧ (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) ∧ (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) ∧ (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V₀ : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → ∃ z : T ⟶ Z, z ≫ i = x) ∧ (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧ ∃ c : (P.pull (lift (snd G (Over.mk (U.ι ≫ T.hom)) ≫ (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ z ≫ i) (fst G (Over.mk (U.ι ≫ T.hom)))).left).Gen, c.IsGen) := by
  intro S' _ G _ _ P hG hP h₁ h₂ hs W hW s hsW
  obtain ⟨V₀, hV₀, hsV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := W) hsW
  obtain ⟨D, _, Q, h, hDab, q, -, hh, e⟩ :=
    GlobalTheory.DualHomPull.exists_dual_hom S' G G (𝟙 G) P hG hG inferInstance hP h₁ h₂
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeAxes.additive_of_triv_axes hG hP h₁ h₂
  have hD : ∀ {Y : Over S'} (a b : Y ⟶ G), evc hP a b = evc q.isLB a (b ≫ h) := fun a b => by
    have e' := (cls_eq_iff (pull_isLB hP _) (pull_isLB q.isLB _)).2 e
    rw [MonoidalCategory.id_tensorHom_id, Over.id_left, cls_pull hP _ (pull_isLB hP _), pull_id,
      cls_pull q.isLB _ (pull_isLB q.isLB _)] at e'
    rw [evc, e', ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, ← Category.assoc, lift_snd]
    rfl
  have K : ∀ {T : Over S'} (x : T ⟶ G), Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left) ↔ x ≫ h = 1 := by
    intro T x
    rw [triv_ev_iff hP, evc_symm hP hs, hD, Category.assoc]
    refine ⟨fun hx => q.eq_one _ ((triv_ev_iff q.isLB _ _).2 hx), fun hx => ?_⟩
    rw [hx, MonObj.comp_one]
    exact evc_one_right q.isLB q.zero _
  have : Mono (η[D]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
  have kerh : ∀ {T : Over S'} (z : T ⟶ pullback h (η[D])), (z ≫ pullback.fst h (η[D])) ≫ h = 1 := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, toUnit_unique (z ≫ pullback.snd _ _) (toUnit _)]
    rfl
  have fac : ∀ {T : Over S'} (x : T ⟶ G), x ≫ h = 1 → ∃ z : T ⟶ pullback h (η[D]), z ≫ pullback.fst h (η[D]) = x :=
    fun x hx => ⟨pullback.lift x (toUnit _) (by rw [hx]; rfl), pullback.lift_fst _ _ _⟩
  have hcl : IsClosedImmersion (pullback.fst h (η[D])).left := by
    have hpb := (IsPullback.of_hasPullback h (η[D])).map (Over.forget S')
    have := hDab.proper
    have : IsClosedImmersion ((η[D]).left ≫ D.hom) := by
      rw [Over.w (η[D])]
      exact (inferInstance : IsClosedImmersion (𝟙 S'))
    have : IsClosedImmersion (η[D]).left := IsClosedImmersion.of_comp _ D.hom
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip this
  refine ⟨V₀, pullback h (η[D]), pullback.fst h (η[D]), hsV, inferInstance,
    GlobalTheory.T.relatively_ample_closed_immersion S' G P hG hP V₀ hV₀ (hW V₀ fun _ hx => hVW hx) _ _ hcl
      (fun T z _ => memKL_of_triv hP hs a₁ a₂ ((K _).2 (kerh z))), ?_, ?_, ?_, ?_, ?_⟩
  · intro T _
    exact fac 1 (MonObj.one_comp h)
  · intro T a b _
    refine fac _ ?_
    rw [MonObj.mul_comp, kerh, kerh, _root_.mul_one]
  · intro T a _
    refine fac _ ?_
    rw [GrpObj.inv_comp, kerh, inv_one]
  · intro T x _ hx
    exact fac x ((K x).1 hx)
  · intro T z _ p
    refine ⟨⊤, trivial, (K _).2 ?_⟩
    rw [Category.assoc, Category.assoc, ← Category.assoc z, kerh, MonObj.comp_one]

end GlobalTheory.KernelNear
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteKernelNearDiagonalAmpleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.exists_finite_kernel_near_diagonal_ample : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → ∀ s ∈ W, ∃ (V₀ : S'.Opens) (Z : Over S') (i : Z ⟶ G), s ∈ V₀ ∧ Mono i ∧ IsFinite (Z.hom ∣_ V₀) ∧ (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) ∧ (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) ∧ (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) ∧ (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V₀ : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → ∃ z : T ⟶ Z, z ≫ i = x) ∧ (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧ ∃ c : (P.pull (lift (snd G (Over.mk (U.ι ≫ T.hom)) ≫ (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ z ≫ i) (fst G (Over.mk (U.ι ≫ T.hom)))).left).Gen, c.IsGen) := by
  first | (exact @GlobalTheory.KernelNear.exists_finite_kernel_near) | (exact GlobalTheory.KernelNear.exists_finite_kernel_near) | (intros; apply GlobalTheory.KernelNear.exists_finite_kernel_near <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenNearOfFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibreOpen

theorem eq_one_of_local {S' : Scheme.{0}} {G : Over S'} [GrpObj G] (T : Over S') (x : T ⟶ G)
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ x = 1) : x = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨U, hp, hx⟩ := h p
  refine ⟨U, hp, ?_⟩
  have h1 : (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ (1 : T ⟶ G) = 1 := MonObj.comp_one _
  rw [← h1] at hx
  exact congrArg (fun q => q.left) hx

theorem unit_residue : ∀ (S' : Scheme.{0}) (W : S'.Opens) (s : S'), s ∈ W → ∀ d : ℕ, IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → IsUnit ((d : ℕ) : S'.residueField s) := by
  intro S' W s hs d hd
  let x : W.toScheme := ⟨s, hs⟩
  have h1 : IsUnit ((d : ℕ) : W.toScheme.residueField x) := by
    have := hd.map (W.toScheme.evaluation ⊤ x trivial).hom
    simpa using this
  have hx : W.ι.base x = s := rfl
  rw [isUnit_iff_ne_zero] at h1 ⊢
  intro h0
  apply h1
  have := congrArg (Scheme.Hom.residueFieldMap W.ι x).hom (hx ▸ h0 : ((d : ℕ) : S'.residueField (W.ι.base x)) = 0)
  simpa using this


open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison GlobalTheory.KerKilledLocal in
theorem kerKilledOn_of_global : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (V : S'.Opens), (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → x ^ d = 1) → GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' G _ _ P V h T x hs
  apply down_injective G V
  rw [down_pow, down_one]
  let T' : Over S' := Over.mk (T.hom ≫ V.ι)
  let GV := (Over.pullback V.ι).obj G
  have hr : Set.range T'.hom.base ⊆ (V : Set S') := by
    rintro _ ⟨t, rfl⟩
    have h' : T'.hom.base t ∈ Set.range V.ι.base := ⟨T.hom.base t, rfl⟩
    rwa [Scheme.Opens.range_ι] at h'
  refine h T' (down G V x) hr ?_
  let Y : Over V.toScheme := Over.mk ((snd G T').left ≫ T.hom)
  have w1 : (fst G T').left ≫ G.hom = (G ⊗ T').hom := Over.w (fst G T')
  have w2 : (snd G T').left ≫ (T.hom ≫ V.ι) = (G ⊗ T').hom := Over.w (snd G T')
  let u : Y ⟶ GV := Over.homMk (pullback.lift (fst G T').left ((snd G T').left ≫ T.hom) (by
      rw [w1, Category.assoc, w2])) (pullback.lift_snd _ _ _)
  let v : Y ⟶ T := Over.homMk (snd G T').left rfl
  have heq : (lift u v).left ≫ (lift (snd GV T ≫ x) (fst GV T)).left ≫ pφ₂ V.ι G =
      (lift (snd G T' ≫ down G V x) (fst G T')).left ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply adelic_GL2_ext_of_local_components G
    · simp only [Category.assoc, pφ₂_fst]
      rw [lift_left_fst'_assoc, lift_left_fst']
      simp only [Over.comp_left, Category.assoc]
      rw [lift_left_snd'_assoc]
      rfl
    · simp only [Category.assoc, pφ₂_snd]
      rw [lift_left_snd'_assoc, lift_left_snd', lift_left_fst'_assoc]
      change pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι = _
      rw [pullback.lift_fst]
  obtain ⟨t, ht⟩ := gen_pull3 P (pφ₂ V.ι G) _ (lift u v).left _ (𝟙 _) heq hs
  exact gen_chartPull (chartPullUnpull _ _ rfl) t ht

theorem comp_pow_overScheme_grpObj {S' : Scheme.{0}} {G T T' : Over S'} [GrpObj G] (u : T' ⟶ T) (x : T ⟶ G) :
    ∀ n : ℕ, u ≫ x ^ n = (u ≫ x) ^ n
  | 0 => by rw [pow_zero, pow_zero, MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj u x n]

theorem kerKilledOn_near_of_fibre : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → ∀ s ∈ W, GlobalTheory.KerKilledNear.FibreKilled d G P s → ∃ V : S'.Opens, s ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' _ G _ _ P hA hP hg₁ hg₂ hsym W hamp hd s hs hfib
  obtain ⟨V₀, Z, i, hs₀, hmono, hfin, h1, hmul, hinv, hfac, hloc⟩ := GlobalTheory.T.exists_finite_kernel_near_diagonal_ample S' G P hA hP hg₁ hg₂ hsym W hamp s hs
  have hfibZ : ∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s),
      T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1 := by
    rintro T z ⟨f, hf⟩
    have hT : Set.range T.hom.base ⊆ (V₀ : Set S') := by
      rintro _ ⟨p, rfl⟩
      have e : (f ≫ S'.fromSpecResidueField s).base p = s :=
        Set.mem_singleton_iff.mp (Scheme.range_fromSpecResidueField s ▸ Set.mem_range_self (f.base p))
      rw [hf, e]
      exact hs₀
    refine eq_one_of_local T _ fun p => ?_
    obtain ⟨U, hp, c, hc⟩ := hloc T z hT p
    refine ⟨U, hp, ?_⟩
    rw [comp_pow_overScheme_grpObj]
    exact hfib (Over.mk (U.ι ≫ T.hom)) _ ⟨U.ι ≫ f, by simp [hf]⟩ ⟨c, hc⟩
  obtain ⟨V, hsV, hVV₀, hV⟩ := GlobalTheory.T.finite_subgroup_killed_near_point_of_fibre S' G Z i V₀ d s hmono hs₀ hfin h1 hmul hinv (unit_residue S' W s hs d hd) hfibZ
  refine ⟨V, hsV, kerKilledOn_of_global d S' G P V fun T x hT hx => ?_⟩
  obtain ⟨z, rfl⟩ := hfac T x (hT.trans hVV₀) hx
  exact hV T z hT

end GlobalTheory.KerKilledFibreOpen
end
end

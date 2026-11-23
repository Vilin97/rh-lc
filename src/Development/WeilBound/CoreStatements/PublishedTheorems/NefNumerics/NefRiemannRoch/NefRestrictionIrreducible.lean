module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
public import Mathlib.Data.ENat.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.HigherCohomologyGrowthStructure
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.HigherCohomologyGrowthTwist
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistPushforwardClosedImmersio

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory

theorem hdim_twist_pushforward_lbPow_of_isClosedImmersion : ∀ (k : Type) [Field k] (X Z : Scheme.{0}) [Algebra k Γ(X, ⊤)] (g : Z ⟶ X) [IsClosedImmersion g] (L : LB X), L.IsLB → ∀ (G : Z.Modules) (m i : ℕ), letI := algebraΓAlong k g; hdim k (twist ((Scheme.Modules.pushforward g).obj G) (lbPow L m)) i = hdim k (twist G (lbPow (L.pull g) m)) i := by
  intro k _ X Z _ g _ L hL G m i
  letI := algebraΓAlong k g
  have hf : ∀ r : k, g.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Z, ⊤) r := fun _ => rfl
  have hP : hdim k ((Scheme.Modules.pushforward g).obj (twist G ((lbPow L m).pull g))) i =
      hdim k (twist G ((lbPow L m).pull g)) i := by
    rw [hdim_def, hdim_def]
    exact (LinearEquiv.ofBijective _
      (cohPushMap_bijective_of_isClosedImmersion k g hf (twist G ((lbPow L m).pull g)) ⊤ i)).finrank_eq
  obtain ⟨e⟩ := nonempty_iso_of_lbIso (F := G) (isLB_lbPow (pull_isLB hL g) m)
    (pull_isLB (isLB_lbPow hL m) g) (lbIso_lbPow_pull hL g m)
  rw [← hdim_congr k i (projIso (lbPow L m) g G), hP, hdim_congr k i e.symm]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistPushforwardClosedImmersioStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_pushforward_closedImmersion : ∀ (k : Type) [Field k] (X Z : Scheme.{0}) [Algebra k Γ(X, ⊤)] (g : Z ⟶ X) [IsClosedImmersion g] (L : LB X), L.IsLB → ∀ (G : Z.Modules) (m i : ℕ), letI := algebraΓAlong k g; hdim k (twist ((Scheme.Modules.pushforward g).obj G) (lbPow L m)) i = hdim k (twist G (lbPow (L.pull g) m)) i := by
  first | exact @GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion | exact GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion | (intros; apply GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistBoundOfShortExact

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_bound_of_shortExact : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (L : LB X), L.IsLB → ∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → ∀ (i : ℕ) (e : ℕ → ℕ), (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₁ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₃ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₂ (lbPow L m)) i ≤ C * e m) := by
  intro k _ _ X _ hX L hL S hS h1 h3 i e hb1 hb3
  obtain ⟨C₁, hC₁⟩ := hb1
  obtain ⟨C₃, hC₃⟩ := hb3
  obtain ⟨hP, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom k X)).1 hX
  have hf := algebraMap_eq_strHom k X
  have F₁ : FiniteCohTwists k S.X₁ := IsAmpleLB.finiteCohTwists hf S.X₁ hA
  have F₃ : FiniteCohTwists k S.X₃ := IsAmpleLB.finiteCohTwists hf S.X₃ hA
  refine ⟨C₁ + C₃, fun m => ?_⟩
  have hLm : (lbPow L m).IsLB := isLB_lbPow hL m
  have hT := Twist.shortExact_map hLm hS
  have fin₁ := ((F₁.twist hLm).finiteCoh).finite i
  have fin₃ := ((F₃.twist hLm).finiteCoh).finite i
  have key := hdim₂_le k hT i fin₁ fin₃
  calc hdim k (twist S.X₂ (lbPow L m)) i ≤ hdim k (twist S.X₁ (lbPow L m)) i + hdim k (twist S.X₃ (lbPow L m)) i := key
    _ ≤ C₁ * e m + C₃ * e m := Nat.add_le_add (hC₁ m) (hC₃ m)
    _ = (C₁ + C₃) * e m := (Nat.add_mul C₁ C₃ (e m)).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistBoundOfShortExactStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_bound_of_shortExact : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (L : LB X), L.IsLB → ∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → ∀ (i : ℕ) (e : ℕ → ℕ), (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₁ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₃ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₂ (lbPow L m)) i ≤ C * e m) := by
  first | exact @GlobalTheory.hdim_twist_bound_of_shortExact | exact GlobalTheory.hdim_twist_bound_of_shortExact | (intros; apply GlobalTheory.hdim_twist_bound_of_shortExact <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestFurther

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Yhb2.main :
    ∀ {a : WithBot ℕ∞} {d : ℕ}, a < (↑(d + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑d : WithBot ℕ∞) := by
  intro a d h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    have h1 : b < ((d+1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have h2 : b ≤ (d : ℕ∞) := by
      induction b using ENat.recTopCoe with
      | top => exact absurd h1 (not_lt.mpr le_top)
      | coe n =>
        have h3 : n < d + 1 := by exact_mod_cast h1
        exact_mod_cast Nat.lt_succ_iff.mp h3
    exact_mod_cast h2
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.HigherCohomologyGrowthStructureStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.higher_cohomology_growth_structure : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @_root_.GlobalTheory.NefRR.hdim_twist_structureModule_le | exact _root_.GlobalTheory.NefRR.hdim_twist_structureModule_le | (intros; apply _root_.GlobalTheory.NefRR.hdim_twist_structureModule_le <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.HigherCohomologyGrowthCoherent

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefBound

theorem le_natCast_of_lt_succ {a : WithBot ℕ∞} {d : ℕ} (h : a < ((d + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (d : WithBot ℕ∞) :=
  _root_.UpperTheory.Reformulated.B.Yhb2.main h

end GlobalTheory.NefBound


open GlobalTheory.VB in
theorem GlobalTheory.NefBound.hdim_twist_le_of_isIntegral : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (G : X.Modules) [IsFiniteQC G], ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist G (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ _ hp d L hL hd hE
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  suffices H : ∀ r : ℕ, ∀ (G : X.Modules) [IsFiniteQC G], genRank G = r → ∀ i, 0 < i →
      ∃ C : ℕ, ∀ m : ℕ, hdim k (twist G (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d) by
    intro G _
    exact H _ G rfl
  intro r
  induction r with
  | zero =>
    intro G _ h i hi
    have hs : suppDim G ≤ (d : WithBot ℕ∞) :=
      GlobalTheory.NefBound.le_natCast_of_lt_succ (suppDim_lt_of_genRank_eq_zero hd h)
    obtain ⟨C, hC⟩ := hE G hs i hi
    refine ⟨C, fun m => (hC m).trans (Nat.mul_le_mul_left _ ?_)⟩
    exact Nat.mul_le_mul (Nat.le_succ d) (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))
  | succ r ih =>
    intro G _ h i hi
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule X).genRank_eq, hr] at e₃
    let S := ShortComplex.mk (QCoh.sectionHom s) (cokernel.π _) (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    have hQ : IsFiniteQC S.X₃ := inferInstanceAs (IsFiniteQC (cokernel (QCoh.sectionHom s)))
    have h1 : IsFiniteQC S.X₁ := inferInstanceAs (IsFiniteQC (structureModule X))
    have hbd : ∀ i, 0 < i → ∃ C : ℕ, ∀ m : ℕ,
        hdim k (twist (twist G (lbPow A n)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d) :=
      fun i hi => GlobalTheory.T.sheafCohomologyDim_twist_bound_of_shortExact k X hp L hL.isLB S hS h1 hQ i _
        (GlobalTheory.T.higher_cohomology_growth_structure k X hp d L hL hd hE i hi) (ih (cokernel (QCoh.sectionHom s)) (by omega) i hi)
    obtain ⟨C, hC⟩ := GlobalTheory.T.higher_cohomology_growth_twist k X hp d L hL.isLB hE (twist G (lbPow A n))
      ((QCoh.suppDim_le _).trans hd) _ (isLB_lbZPow hM (-1)) hbd i hi
    refine ⟨C, fun m => ?_⟩
    exact (hdim_congr k i ((twistFunctor (lbPow L m)).mapIso (Twist.twistTwistZNegOneIso G hM))).symm.trans_le (hC m)
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.HigherCohomologyGrowthCoherentStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.higher_cohomology_growth_coherent : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), IsNef k L → topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (G : X.Modules) [IsFiniteQC G], ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist G (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @_root_.GlobalTheory.NefBound.hdim_twist_le_of_isIntegral | exact _root_.GlobalTheory.NefBound.hdim_twist_le_of_isIntegral | (intros; apply _root_.GlobalTheory.NefBound.hdim_twist_le_of_isIntegral <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRestrictionIrreducible

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RRPush

theorem hdim_pushforward_le : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → ∀ N : LB Y, IsNef k N → ∀ (E : Y.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow N m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ L : LB X, IsNef k L → ∀ Z : Closeds X, IsIrreducible (Z : Set X) → topologicalKrullDim (Z : Set X) ≤ (d + 1 : ℕ) → ∀ (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [IsFiniteQC G], ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist ((Scheme.Modules.pushforward (redι Z)).obj G) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ d hY X _ hp L hL Z hZ hd G _ i hi
  haveI := isIntegral_red hZ
  letI := algebraΓAlong k (redι Z)
  have hk := appTop_algebraMap_along k (redι Z)
  have hp' : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    obtain ⟨n, e, he, hs⟩ := hp
    exact ⟨n, redι Z ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom hk]⟩
  have hLZ : IsNef k (L.pull (redι Z)) := hL.pull_of_isClosedImmersion (redι Z) hk
  have hdV : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (d + 1 : ℕ) :=
    (topologicalKrullDim_red Z).trans_le hd
  obtain ⟨C, hC⟩ := GlobalTheory.T.higher_cohomology_growth_coherent k _ hp' d (L.pull (redι Z)) hLZ hdV
    (fun E _ hE j hj => hY _ hp' _ hLZ E hE j hj) G i hi
  refine ⟨C, fun m => ?_⟩
  rw [GlobalTheory.T.sheafCohomologyDim_twist_pushforward_closedImmersion k X _ (redι Z) L hL.isLB G m i]
  exact hC m

end GlobalTheory.RRPush
end
end
end

module

public import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemCrit
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesAdmittedOfLevels
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPrimOfGood
import Formalism.SharpRestriction.LevelLetterCocycles.DvOZeroHigh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.TmulMemFilV
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow
public import Formalism.SharpRestriction.LevelLetterCocycles.IntAOfNonpol
public import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
public import Formalism.SharpRestriction.LevelLetterCocycles.SplittingOfExactnessAndData
public import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelSeriesFirstFactorOrderOne
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ConstantCoeffQZeroEqP
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.PolarToPoleOfCtx

section

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

theorem dvO_zero_hw (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (T : LocLat G Qp LL O)
    (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ)
    (a : ZMod n) (s : ℕ) (u : ℤ) (hu : (Hw A.G₀ A.S A.η (A.ty (a - (s : ZMod n))) : ℤ) < u)
    (c₀ : Fin d → O) (h : dvO W T e b c₀ ∈ FilS W T a s u) : c₀ = 0 := by
  obtain ⟨y, ⟨hyF, hyD⟩, hye⟩ := h
  set i : ZMod n := a - (s : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W C.hbij i
  have hJ : ∀ z, IsJumpV PD T.ρ τ z → z ≤ (Hw A.G₀ A.S A.η (A.ty i) : ℤ) := fun z hz =>
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ z hz)).2
  have hy0 := fil_high W T i τ hover C.hbij.2 _ hJ u hu hyD hyF
  rw [hy0, map_zero] at hye
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W C.hs C.hV T (C.h3 T hT.1)
    (C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)) (C.hmod T hT.1) c' e b hb).1
  have hdv : dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]; rfl
  have hsum : ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) = 0 := by rw [← hdv, ← hye]
  funext m
  apply C.hinj
  rw [Fintype.linearIndependent_iff.1 hfb _ hsum m]
  simp

theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u w : ℤ} (h : w ≤ u) :
    FilS W T a s u ≤ FilS W T a s w := by
  apply Submodule.map_mono
  intro x hx
  exact ⟨Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h hx.1, hx.2⟩

theorem inId_zero (a : ZMod n) (e : ℕ) : InId W a e (fun _ => 0) 0 :=
  ⟨0, W.AΔ.zero_mem, by simp⟩

theorem condPole_of_polar (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (T : LocLat G Qp LL O)
    (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (c : ZMod n)
    (α : ℕ → ℤ) (c₀ : Fin d → O) (hc₀ : c₀ ≠ 0)
    (hP : Formalism.MainNotions.UnusedSlot80.LevC.condPolar (W := W) T c (A.len c) b α c₀) :
    condPole W A T c b α c₀ := by
  intro s hs
  have key : 0 ≤ α s ∨ -(Hw A.G₀ A.S A.η (A.ty (c - (s : ZMod n))) : ℤ) ≤ α s ∧
      dvO W T (A.len c) b c₀ ∈ FilS W T c s (-(α s)) := by
    rcases hP s hs with h | h
    · exact Or.inl h
    · by_cases h0 : 0 ≤ α s
      · exact Or.inl h0
      · refine Or.inr ⟨?_, h⟩
        by_contra hlt
        exact hc₀ (dvO_zero_hw W C A hA c' T hT b hb (A.len c) c s (-(α s)) (by omega) c₀ h)
  cases hty : A.ty (c - (s : ZMod n)) with
  | thin =>
    rw [hty] at key
    simp only [Hw] at key
    rcases key with h | ⟨h, -⟩ <;> omega
  | up bs =>
    rw [hty] at key
    simp only [Hw] at key
    rcases key with h | ⟨h, -⟩ <;> push_cast at h ⊢ <;> omega
  | down bs =>
    rcases key with h | ⟨-, h⟩
    · exact Or.inl h
    · by_cases h0 : 0 ≤ α s
      · exact Or.inl h0
      · exact Or.inr (filS_anti W T c s (by omega) h)

variable {W}

theorem polarToPole_of_ctx (C : Ctx W) : Formalism.MainNotions.UnusedSlot80.Split.PolarToPole W := by
  intro _ _ A hA T₂ hT c hc d b sol hb f hS
  obtain ⟨I, g, c₀, α, hg, hF⟩ := hS
  refine ⟨I, fun i => if c₀ i = 0 then 0 else g i, c₀, fun i => if c₀ i = 0 then fun _ => 0 else α i,
    fun i => ?_, fun k => ?_⟩
  · by_cases h0 : c₀ i = 0
    · simp only [h0, if_true]
      refine ⟨inId_zero W c (A.len c), ?_⟩
      intro s _
      cases A.ty (c - (s : ZMod n)) with
      | thin => simp
      | up bs => simp
      | down bs => exact Or.inl le_rfl
    · simp only [h0, if_false]
      exact ⟨(hg i).1, condPole_of_polar W C A hA _ T₂ hT b hb.1 c (α i) (c₀ i) h0 (hg i).2⟩
  · rw [hF k]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : c₀ i = 0
    · simp [h0]
    · simp [h0]

end Formalism.MainNotions.UnusedSlot80.LevC

namespace Formalism.MainNotions.UnusedSlot80.Split

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem polarToPoleL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmArcA D HW F Cm) : PolarToPoleL D HW := by
  intro l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  exact LevC.polarToPole_of_ctx (ctx_of D HW F Cm h l K LL hG hCA h5l)

end Formalism.MainNotions.UnusedSlot80.Split
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.SplitPolarLOf

section

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

variable [IsDomain O] [NeZero n]

theorem splitPolar_of [FiniteDimensional Qp LL] (C : LevC.Ctx W) (hArc : ArcCore W)
    (hJ : Formalism.MainNotions.LiftingTheory.coreJumps PD LL O) (h9 : DcrisExactStrict PD LL) : Split.SplitPolar W := by
  intro _ _ A hA T₂ Y ι π hT₂ hY hses c hc w hI hP hpx d b sol hb
  obtain ⟨p, hp, x, hx, hpx⟩ := hpx
  have hac : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c := sub_add_cancel _ _
  have hc' : c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts := ((hA.2.2.1 c hc).2.2).1
  have hje : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hWY : Win W A Y := Formalism.MainNotions.UnusedSlot80.Split2.win_ext W A hJ (Formalism.MainNotions.LiftingTheory.lone_HOne0 W) hT₂ hY hses
  obtain ⟨dY, bY, hbYf⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W Y (c - ((A.len c : ℕ) : ZMod n)) (C.hmod Y hY)
  obtain ⟨solY, hbY⟩ := Formalism.MainNotions.UnusedSlot80.UnivF.hor_exists W C.hH C.hCA Y hY _ bY hbYf
  obtain ⟨-, hAC⟩ := hArc C.hCA C.h5p A hA c hc (A.len c) hje le_rfl
  obtain ⟨-, -, -, h2f⟩ := hAC T₂ hT₂
  obtain ⟨⟨hind2, hspan2⟩, -⟩ := h2f d b sol hb
  obtain ⟨-, -, -, hYf⟩ := hAC Y hWY
  obtain ⟨⟨hindY, hspanY⟩, -, -, hNY, -⟩ := hYf dY bY solY hbY
  rw [hac] at hspan2 hspanY hNY
  have hxe : x = p - W.map ι w := by rw [hpx]; abel
  have hxN : InFNc W Y c 1 x := by
    refine ⟨x, ⟨Formalism.MainNotions.UnusedSlot80.Split2.N_of_Nl W hx, fun δ hδ => ?_⟩,
      Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W Y c hx, (one_smul _ _).symm⟩
    rw [hxe, map_sub, Formalism.MainNotions.UnusedSlot80.Relay2.Pp_Δ W Y _ _ p hp δ hδ, ← W.map_γ, hI.2.1 δ hδ]
  exact polar_core W C h9 A hA _ hc' (A.len c) c hac T₂ Y ι π hT₂ hWY hses b sol hb bY solY hbY hind2 hspan2
    hindY hspanY hNY w p x hP hp hxN hpx

end Formalism.MainNotions.UnusedSlot80.SplitP

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem splitPolarL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmArcA D HW F Cm) (hArc : ArcCoordinatesTheorem D HW F Cm) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (h9 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D) : Split.SplitPolarL D HW := by
  intro l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have C := ctx_of D HW F Cm hAdm l K LL hG hCA h5l
  exact SplitP.splitPolar_of _ C ((hArc hAdm) l K LL hG hCA h5l).1 (h23 l K LL) (h9 l K LL)

end Formalism.MainNotions.UnusedSlot80
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.SplitShapeLRec

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem splitShapeL_rec (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hArc : AdmArcA D HW F Cm) (h1 : LevelZeroModPLocal D HW) (h2 : LevelZeroModPRefinedLocal D HW) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (h9 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D) : Split.SplitShapeL D HW :=
  Split.splitShapeL_of_pieces D HW (splitPolarL_of D HW F Cm hArc (arc_coordinates_of_levels D HW F Cm h1 h2) h23 h9)
    (Split.polarToPoleL_of D HW F Cm hArc)

end Formalism.MainNotions.UnusedSlot80
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.SplittingOfLiteratureExactness

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem ddExactL_of_litFont (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : Split.DDExactL D HW := by
  intro l _ K LL hG hCA _ T₂ Y ι π _ _ hses
  obtain ⟨hinj, -, hker⟩ := (h l K LL hCA).2.1 T₂ Y _ ι π hses
  refine ⟨fun x => (hker _).2 ⟨x, rfl⟩, fun x hx => hinj (by rw [hx, map_zero]), fun u hu => (hker u).1 hu⟩

theorem splitting_of_literature_exactness (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : AdmSplitA D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hS : Split.SplitShapeL D HW) : SplittingArcLifting D HW F Cm :=
  splitting_general_of_exactness D HW F Cm hA h6 hH hTr hWX (ddExactL_of_litFont D HW F hFont) hS

end Formalism.MainNotions.UnusedSlot80
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrobeniusLevels

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem arc_coordinates_of_frobenius (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (h2 : LevelZeroModPRefinedLocal D HW) : ArcCoordinatesTheorem D HW F Cm := fun hA =>
  arc_coordinates_of_levels D HW F Cm (lev0MpL_of D HW F Cm hA h4 h9) h2 hA

theorem arc_coordinates_of_frobenius_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hA : AdmArcA D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h2 : LevelZeroModPRefinedLocal D HW) : ArcLiftingCoordinates D HW F Cm :=
  arc_coordinates_of_frobenius D HW F Cm h4 h9 h2 hA

theorem split_case_A_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hA : AdmSplitA D HW F Cm) (hArc : AdmArcA D HW F Cm)
    (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (h17 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D)
    (h2 : LevelZeroModPRefinedLocal D HW) : SplittingArcLifting D HW F Cm :=
  splitting_of_literature_exactness D HW F Cm hA h6 hH hTr hWX hFont
    (splitShapeL_rec D HW F Cm hArc (lev0MpL_of D HW F Cm hArc h4 h9) h2 h23 h17)

end Formalism.MainNotions.UnusedSlot80
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesFinal

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module Formalism.MainNotions.N.Pv.LocalLengthBound.Ser Formalism.MainNotions.N.Pv.LocalLengthBound.MC

section Pf

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {PD : PeriodData G Qp K₀ K B BdR}
    (W : LocWach PD LL O v n)

theorem memCrit_of_free [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hFr : IsFractionRing O LL)
    (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : MemCrit W := by
  apply Formalism.MainNotions.N.Pv.LocalLengthBound.memCrit_of <;> assumption

end Pf

theorem memCritL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1f : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
      haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
      MemCrit ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5l
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  have hCW : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hG) :=
    Formalism.MainNotions.UnusedSlot80.caseA_of_unram' (D.loc l) (HW l) hG hCA.1 hCA.2.1
  have hLev := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm h4 (Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F h9) l K LL hCA h5l
  exact memCrit_of_free _ hCW (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL) (h1f l K 1 LL hG) (h3 l K 1 LL hG) hLev
    (h5 l K 1 LL hG) (h11 l K LL).2.2

end Formalism.MainNotions.N.Pv.LocalLengthBound

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem arc_coordinates_final (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : AdmArcA D HW F Cm) (h1f : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    ArcLiftingCoordinates D HW F Cm :=
  arc_coordinates_of_frobenius_levels D HW F Cm hA hA.2.1 hA.2.2.2.1
    (lev0MprL_of D HW F Cm hA (Formalism.MainNotions.N.Pv.LocalLengthBound.memCritL_of D HW F Cm h1f hA.1 hA.2.1 hA.2.2.1 hA.2.2.2.1 h11))

theorem split_case_A_final (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : AdmSplitA D HW F Cm) (hArc : AdmArcA D HW F Cm) (h1f : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F)
    (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (h17 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    SplittingArcLifting D HW F Cm :=
  split_case_A_of_hypotheses D HW F Cm hA hArc hArc.2.1 h6 hArc.2.2.2.1 hArc.2.2.2.2.1 hArc.2.2.2.2.2.1 hWX hFont h23 h17
    (lev0MprL_of D HW F Cm hArc
      (Formalism.MainNotions.N.Pv.LocalLengthBound.memCritL_of D HW F Cm h1f hArc.1 hArc.2.1 hArc.2.2.1 hArc.2.2.2.1 h11))

end Formalism.MainNotions.UnusedSlot80
end
end
end

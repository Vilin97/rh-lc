module

import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepIntegrandFiniteDoubleCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepIntegrandInvariantAtSuccPlacesStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureQuotientGroupProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixProjEqOneOfSuppAtDistinctFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMemStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedInnerIntegralAtFirstOfSplitPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueSuccPlacesOuterStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureQuotientGroupProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.haar_measure_quotient_group_product : ∀ (A₁ : Type) [Group A₁] [TopologicalSpace A₁] [IsTopologicalGroup A₁] [SecondCountableTopology A₁] [LocallyCompactSpace A₁] [T2Space A₁] [MeasurableSpace A₁] [BorelSpace A₁] (B₁ : Type) [Group B₁] [TopologicalSpace B₁] [IsTopologicalGroup B₁] [SecondCountableTopology B₁] [LocallyCompactSpace B₁] [T2Space B₁] [MeasurableSpace B₁] [BorelSpace B₁] (A₂ : Type) [Group A₂] [TopologicalSpace A₂] [IsTopologicalGroup A₂] [SecondCountableTopology A₂] [LocallyCompactSpace A₂] [T2Space A₂] [MeasurableSpace A₂] [BorelSpace A₂] (B₂ : Type) [Group B₂] [TopologicalSpace B₂] [IsTopologicalGroup B₂] [SecondCountableTopology B₂] [LocallyCompactSpace B₂] [T2Space B₂] [MeasurableSpace B₂] [BorelSpace B₂] (R₁ : Subgroup A₁) (S₁ : Subgroup B₁) (R₂ : Subgroup A₂) (S₂ : Subgroup B₂), IsClosed (R₁ : Set A₁) → IsClosed (S₁ : Set B₁) → IsClosed (R₂ : Set A₂) → IsClosed (S₂ : Set B₂) → ∀ (a₁ : Measure A₁) (b₁ : Measure B₁) (a₂ : Measure A₂) (b₂ : Measure B₂) (r₁ : Measure R₁) (s₁ : Measure S₁) (r₂ : Measure R₂) (s₂ : Measure S₂) (p₁ : Measure (R₁.prod S₁)) (p₂ : Measure (R₂.prod S₂)), a₁.IsHaarMeasure → b₁.IsHaarMeasure → a₂.IsHaarMeasure → b₂.IsHaarMeasure → r₁.IsHaarMeasure → s₁.IsHaarMeasure → r₂.IsHaarMeasure → s₂.IsHaarMeasure → r₁.IsInvInvariant → s₁.IsInvInvariant → r₂.IsInvInvariant → s₂.IsInvInvariant → p₁.map (R₁.prodEquiv S₁) = r₁.prod s₁ → p₂.map (R₂.prodEquiv S₂) = r₂.prod s₂ → ∀ (K₁ : Subgroup A₁) (L₁ : Subgroup B₁) (K₂ : Subgroup A₂) (L₂ : Subgroup B₂), IsCO K₁ → IsCO L₁ → IsCO K₂ → IsCO L₂ → ∀ f : A₁ × B₁ → A₂ × B₂ → ℂ, (∀ x y, ∀ r ∈ R₂.prod S₂, ∀ κ ∈ K₂.prod L₂, f x (r * y * κ) = f x y) → (∀ x y, ∀ κ ∈ K₁.prod L₁, f (x * κ) y = f x y) → (∀ x y, ∀ r ∈ R₁.prod S₁, f (r * x) y = f x y) → (∃ T : Finset (A₁ × B₁), ∀ x y, f x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ R₁.prod S₁, ∃ κ ∈ K₁.prod L₁, x = r * t * κ) → (∀ x, ∃ T : Finset (A₂ × B₂), ∀ y, f x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ R₂.prod S₂, ∃ κ ∈ K₂.prod L₂, y = r * t * κ) → ∀ (g : A₁ → A₂ → ℂ) (z : ℂ), (∀ x y, Iter2 s₁ b₁ s₂ b₂ (fun x' y' => f (x, x') (y, y')) (g x y)) → Iter2 r₁ a₁ r₂ a₂ g z → Iter2 p₁ (a₁.prod b₁) p₂ (a₂.prod b₂) f z := by
  first | exact @GlobalTheory.IterPeel.iterated_integral_product_groups | exact GlobalTheory.IterPeel.iterated_integral_product_groups | (intros; apply GlobalTheory.IterPeel.iterated_integral_product_groups <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactOpenProductLevelsFamily

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QVal.LevCO

variable {D : D7}

theorem isCO_iSup_map (V : HSp D) {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i))
    (hq : Function.Injective fun i => (q i).v) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i)) (gl : ∀ i, GL (Y i) (k i) →* GA D V)
    (hgl : ∀ i g, SuppAt (q i).e V (gl i g) ∧ (mt V (gl i g)).map (q i).pr = (F i).β * g.val * (F i).γ)
    (L : ∀ i, Subgroup (GL (Y i) (k i))) (hL : ∀ i, IsCO (L i)) :
    IsCO ((⨆ i, (L i).map (gl i)).subgroupOf (GlobalTheory.FinPl.grpAt V (fun p => ∃ i, (q i).v = p))) := by
  set P : GlobalTheory.FinPl.Pl D → Prop := fun p => ∃ i, (q i).v = p with hPdef
  have hA : GlobalTheory.FinPl.grpAt V P = GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v) := by
    congr 1
    funext p
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  obtain ⟨Ψ, hc, -, -, huniq⟩ := GlobalTheory.FixLev.exists_section V k q hq Y F
  let lh : ∀ i, GA D V →* GL (Y i) (k i) := fun i => GlobalTheory.FixLev.locHom (q i) V (F i)
  have hlh_self : ∀ i g, lh i (gl i g) = g := fun i g =>
    Units.ext (GlobalTheory.FixLev.frame_cancel (F i) ((GlobalTheory.FixLev.locHom_spec _ _ _ _).symm.trans (hgl i g).2))
  have hmat_ne : ∀ i j, i ≠ j → ∀ g, (mt V (gl j g)).map (q i).pr = 1 := fun i j hij g =>
    GlobalTheory.T.matrix_proj_eq_one_of_suppAt_distinct_finitePlace D (k i) (k j) (q i) (q j) V (gl j g) (fun e => hij (hq e)) (hgl j g).1
  have hlh_ne : ∀ i j, i ≠ j → ∀ g, lh i (gl j g) = 1 := fun i j hij g => Units.ext (by
    show (F i).γ * (mt V (gl j g)).map (q i).pr * (F i).β = 1
    rw [hmat_ne i j hij g, Matrix.mul_one, (F i).γβ])
  set H := ⨆ i, (L i).map (gl i) with hHdef
  have hglA : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt V P := fun i g =>
    GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem D (k i) (q i) V _ (hgl i g).1 P ⟨i, rfl⟩
  have hHL : ∀ x ∈ H, ∀ i, lh i x ∈ L i := by
    intro x hx i
    have hle : H ≤ (L i).comap (lh i) := iSup_le fun j => Subgroup.map_le_iff_le_comap.2 fun g hg => by
      show lh i (gl j g) ∈ L i
      by_cases hij : i = j
      · subst hij
        rw [hlh_self]
        exact hg
      · rw [hlh_ne i j hij]
        exact one_mem _
    exact hle hx
  let Φ : (∀ i, GL (Y i) (k i)) → GA D V := fun y => ((List.finRange r).map fun i => gl i (y i)).prod
  have hΦA : ∀ y, Φ y ∈ GlobalTheory.FinPl.grpAt V P := fun y =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact hglA i (y i)
  have hΦH : ∀ y, (∀ i, y i ∈ L i) → Φ y ∈ H := fun y hy =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map_of_mem _ (hy i))
  have hΦloc : ∀ y i, (mt V (Φ y)).map (q i).pr = (F i).β * (y i).val * (F i).γ := fun y i => by
    show (mt V ((List.finRange r).map fun i => gl i (y i)).prod).map (q i).pr = _
    rw [GlobalTheory.FixLev.map_mt_list_prod, List.map_map]
    exact (GlobalTheory.FixLev.list_prod_single (fun i' => (mt V (gl i' (y i'))).map (q i).pr) i
      (fun i' hi' => hmat_ne i i' (Ne.symm hi') _) _ (List.nodup_finRange r) (List.mem_finRange i)).trans
      (hgl i (y i)).2
  have hΨΦ : ∀ y, Ψ y = Φ y := fun y => huniq (Φ y) (by rw [← hA]; exact hΦA y) y (hΦloc y)
  have hx_eq : ∀ x ∈ GlobalTheory.FinPl.grpAt V P, Ψ (fun i => lh i x) = x := fun x hx =>
    huniq x (by rw [← hA]; exact hx) _ fun i => GlobalTheory.FixLev.locHom_spec _ _ _ x
  have hmem : ∀ x : GlobalTheory.FinPl.grpAt V P, (x : GA D V) ∈ H ↔ ∀ i, lh i x ∈ L i := fun x =>
    ⟨fun h => hHL _ h, fun h => by rw [← hx_eq x x.2, hΨΦ]; exact hΦH _ h⟩
  refine ⟨?_, ?_⟩
  · have hset : ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P)) =
        ⋂ i, (fun g : GlobalTheory.FinPl.grpAt V P => lh i g.1) ⁻¹' (L i : Set _) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_iInter, Set.mem_preimage]
      exact hmem g
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hL i).1.preimage ((GlobalTheory.FixLev.continuous_locHom _ _ _).comp continuous_subtype_val)
  · rw [Subtype.isCompact_iff]
    have himg : (((↑) : GlobalTheory.FinPl.grpAt V P → GA D V) ''
        ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P))) =
        Ψ '' Set.pi Set.univ fun i => (L i : Set _) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : (x : GA D V) ∈ H := Subgroup.mem_subgroupOf.1 hx
        exact ⟨fun i => lh i x, fun i _ => hHL _ hx' i, hx_eq x x.2⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨Ψ y, ?_⟩, ?_, rfl⟩
        · rw [hΨΦ]
          exact hΦA y
        · show Ψ y ∈ H
          rw [hΨΦ]
          exact hΦH y fun i => hy i (Set.mem_univ _)
    rw [himg]
    exact (isCompact_univ_pi fun i => (hL i).2).image hc

theorem isCO_levJ_levB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) → IsCO (levJ Q) ∧ IsCO (levB Q) := by
  intro D ψ σ S r Q hinj
  exact ⟨isCO_iSup_map S.J.W (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₁) (fun i => (Q i).gl₁)
      (fun i g => (Q i).loc₁ g) (fun i => (Q i).L₁.J) (fun i => (Q i).co₁),
    isCO_iSup_map S.B'.V (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₂) (fun i => (Q i).gl₂)
      (fun i g => (Q i).loc₂ g) (fun i => (Q i).L₂.J) (fun i => (Q i).co₂)⟩

end GlobalTheory.QVal.LevCO

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactOpenProductLevelsFamilyStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.isCompactOpen_product_levels_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S), Function.Injective (fun i => (Q i).q.v) → IsCO (levJ Q) ∧ IsCO (levB Q) := by
  first | exact @GlobalTheory.QVal.LevCO.isCO_levJ_levB | exact GlobalTheory.QVal.LevCO.isCO_levJ_levB | (intros; apply GlobalTheory.QVal.LevCO.isCO_levJ_levB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueAtRPlacesZero

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QVal

theorem quotient_integral_of_subsingleton {G : Type} [Group G] [MeasurableSpace G] [Subsingleton G] {R : Subgroup G}
    (μR : Measure R) (μG : Measure G) (hR : μR Set.univ = 1) (hG : μG Set.univ = 1) (f : G → ℂ) :
    IsQuotIntL1 μR μG f (f 1) := by
  haveI : IsProbabilityMeasure μR := ⟨hR⟩
  haveI : IsProbabilityMeasure μG := ⟨hG⟩
  have hc : ∀ x, f x = f 1 := fun x => by rw [Subsingleton.elim x 1]
  have hf : f = fun _ => f 1 := funext hc
  refine ⟨fun _ => f 1, integrable_const _, fun _ => integrable_const _, fun h => ?_, ?_⟩
  · simp [hc h]
  · simp

section
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem conv_nil' {G : Type} [Monoid G] : conv ([] : List (G →₀ ℂ)) = Finsupp.single 1 1 := rfl

theorem aconv_singleton' {G : Type} [AddMonoid G] (c : G →₀ ℂ) : aconv [c] = c := by
  simp only [aconv, List.foldr_cons, List.foldr_nil]
  conv_rhs => rw [← Finsupp.sum_single c]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem aconv_nil' {G : Type} [AddMonoid G] : aconv ([] : List (G →₀ ℂ)) = Finsupp.single 0 1 := rfl

theorem comb_single_zero' (S' T : HSp D) (u : WO S' T → ℂ) :
    comb ψ S' T (Finsupp.single 0 1) u = u := by
  simp [comb, Finsupp.support_single_ne_zero _ one_ne_zero, heisO_zero_eq]

theorem trc_single_one' {V : HSp D} (u : GA D V → ℂ) : trc (Finsupp.single 1 1) u = u := by
  simp only [trc, Finsupp.support_single_ne_zero (1 : GA D V) (one_ne_zero (α := ℂ)), Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext x
  show u (x * 1) = u x
  rw [mul_one]

theorem value_zero_eq (Q : Fin 0 → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ = integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ 1 1 := by
  simp only [value, integrand, List.ofFn_zero, conv_nil', aconv_singleton', trc_single_one']
  rw [GlobalTheory.PosOne.comb, Finsupp.sum_single_index (by simp)]
  simp [aconv_nil', comb_single_zero']
end

end GlobalTheory.QVal

namespace GlobalTheory.QVal

theorem valQr_zero : ∀ D : D7, ValQr D 0 := by
  intro D ψ _ σ S Q _ μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ _
  obtain ⟨-, -, -, -, e1, e2, e3, e4⟩ := hN
  have hP : ¬ ∃ v, places Q v := fun ⟨_, i, _⟩ => i.elim0
  haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.J.W (places Q)) := by
    rw [grpAt_eq_bot S.J.W hP]; infer_instance
  haveI : Subsingleton (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) := by
    rw [grpAt_eq_bot S.B'.V hP]; infer_instance
  simp only [IsEmpty.forall_iff, Set.setOf_true] at e1 e2 e3 e4
  refine ⟨fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1, ?_, fun q => ?_⟩
  · have := quotient_integral_of_subsingleton ρ₁ μ₁ e2 e1 (fun x => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 1)
    simpa [value_zero_eq] using this
  · have := quotient_integral_of_subsingleton ρ₂ μ₂ e4 e3 (fun y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ q.1 y.1)
    simpa using this

end GlobalTheory.QVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueAtRPlacesZeroStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.iteratedIntegralValueAtRPlaces_zero : ∀ D : D7, ValQr D 0 := by
  first | exact @GlobalTheory.QVal.valQr_zero | exact GlobalTheory.QVal.valQr_zero | (intros; apply GlobalTheory.QVal.valQr_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySuccStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.periodGroups_reduce_splitPlaceFamily_succ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ (μ₁ : Measure (grpAt S.J.W (places Q))) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places Q)))) (μ₂ : Measure (grpAt S.B'.V (places Q))) (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places Q)))), Norm Q μ₁ ρ₁ μ₂ ρ₂ → LocallyCompactSpace (grpAt S.J.W (places fun i => Q i.succ)) ∧ LocallyCompactSpace (grpAt S.B'.V (places fun i => Q i.succ)) ∧ IsClosed (((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ)) : Set (grpAt S.J.W (places fun i => Q i.succ)))) ∧ IsClosed (((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ)) : Set (grpAt S.B'.V (places fun i => Q i.succ)))) ∧ IsClosed ((RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1) : Set (GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k))) ∧ IsClosed ((R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1) : Set (GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k))) ∧ ∃ (μ₁' : Measure (grpAt S.J.W (places fun i => Q i.succ))) (ρ₁' : Measure ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ)))) (μ₂' : Measure (grpAt S.B'.V (places fun i => Q i.succ))) (ρ₂' : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ)))) (m₁ : Measure (GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k)) (s₁ : Measure (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1))) (m₂ : Measure (GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k)) (s₂ : Measure (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1))) (p₁ : Measure (((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ))).prod (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1)))) (p₂ : Measure (((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ))).prod (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1)))), Norm (fun i => Q i.succ) μ₁' ρ₁' μ₂' ρ₂' ∧ LocNorm (Q 0) m₁ s₁ m₂ s₂ ∧ ρ₁'.IsInvInvariant ∧ ρ₂'.IsInvInvariant ∧ s₁.IsInvInvariant ∧ s₂.IsInvInvariant ∧ p₁.map (Subgroup.prodEquiv _ _) = ρ₁'.prod s₁ ∧ p₂.map (Subgroup.prodEquiv _ _) = ρ₂'.prod s₂ ∧ ∀ (F : GA D S.J.W → GA D S.B'.V → ℂ) (z : ℂ), Iter2 p₁ (μ₁'.prod m₁) p₂ (μ₂'.prod m₂) (fun x y => F (x.1.1 * (Q 0).gl₁ x.2) (y.1.1 * (Q 0).gl₂ y.2)) z → Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => F x.1 y.1) z := by
  first | exact @GlobalTheory.QRed.reduce | exact GlobalTheory.QRed.reduce | (intros; apply GlobalTheory.QRed.reduce <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepAdelicIntegralFiniteTwistPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QVal

theorem valQr_succ (D : D7) (r : ℕ) (IH : ValQr D r) : ValQr D (r + 1) := by
  intro ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  obtain ⟨lc₁, lc₂, cl₁, cl₂, cl₃, cl₄, μ₁', ρ₁', μ₂', ρ₂', m₁, s₁, m₂, s₂, p₁, p₂, hN', hL, i₁, i₂, i₃, i₄, e₁, e₂, hred⟩ :=
    GlobalTheory.T.periodGroups_reduce_splitPlaceFamily_succ D ψ σ S r Q hinj μ₁ ρ₁ μ₂ ρ₂ hN
  have hN'' := hN'
  obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := hN''
  have hL' := hL
  obtain ⟨b1, -, b3, -, b5, -, b7, -⟩ := hL'
  obtain ⟨co₁, co₂⟩ := GlobalTheory.T.isCompactOpen_product_levels_family D ψ σ S r (fun i => Q i.succ) (hinj.comp (Fin.succ_injective _))
  obtain ⟨v1, v2, v3⟩ := GlobalTheory.T.doubleThetaStep_integrand_invariant_at_succ_places D ψ hψ σ S r Q hinj c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  obtain ⟨n1, n2⟩ := GlobalTheory.T.doubleThetaStep_integrand_finite_doubleCosets D ψ hψ σ S r Q hinj c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  apply hred (integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂)
  haveI := lc₁
  haveI := lc₂
  haveI : BorelSpace (GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k) := GlobalTheory.SplitFlip.borel_GL
  exact GlobalTheory.T.haar_measure_quotient_group_product _ _ _ _ _ _ _ _ cl₁ cl₃ cl₂ cl₄ μ₁' m₁ μ₂' m₂ ρ₁' s₁ ρ₂' s₂ p₁ p₂ a1 b1 a3 b5 a2 b3 a4 b7 i₁ i₃ i₂ i₄
    e₁ e₂ _ _ _ _ co₁ (Q 0).co₁ co₂ (Q 0).co₂ (pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) v1 v2 v3 n1 n2
    (fun x y => innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) _
    (fun x y => GlobalTheory.T.iteratedInnerIntegral_at_first_of_splitPlaces D ψ hψ σ S r Q hinj m₁ s₁ m₂ s₂ hL c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH x.1 x.2 y.1 y.2)
    (GlobalTheory.T.iteratedIntegralValue_succ_places_outer D r IH ψ hψ σ S Q hinj μ₁' ρ₁' μ₂' ρ₂' hN' c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH)

theorem valQ : ∀ D : D7, ValQ D := fun D => valQ_of_valQr D fun r => by
  induction r with
  | zero => exact GlobalTheory.T.iteratedIntegralValueAtRPlaces_zero D
  | succ r ih => exact valQr_succ D r ih

end GlobalTheory.QVal
end
end
end

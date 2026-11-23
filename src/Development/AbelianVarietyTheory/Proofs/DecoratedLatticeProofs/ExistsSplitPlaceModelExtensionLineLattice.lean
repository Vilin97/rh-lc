module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.LocallyConstant.Algebra

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzBruhatExtByZeroOfSplitPlaceHalf

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.SBOfHalf

theorem exists_sb_ext_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  intro D k _ _ _ _ p S T Y Y' _ _ _ _ FS FT Λ hAo hAc Φ hΦ
  classical
  set A : AddSubgroup (Matrix Y Y' k) := Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) with hA
  obtain ⟨hsupp, k₀, hk₀, hinv, hsup⟩ := hΦ
  have hkF : ((k₀ : D.host.F)) ≠ 0 := Nat.cast_ne_zero.2 hk₀.ne'
  have hkk : ((k₀ : k)) ≠ 0 := by
    have h := (map_ne_zero (p.π.comp (algebraMap D.host.F (AE D)))).2 hkF
    simpa using h
  have hupA : ∀ a : Matrix Y Y' k, a ∈ A ↔ p.up FS FT a ∈ Λ := fun a => Iff.rfl
  have hnsmul : ∀ (x : Matrix Y Y' k), k₀ • x = (k₀ : k) • x := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k]
  have hup_nsmul : ∀ (x : Matrix Y Y' k), p.up FS FT (k₀ • x) = k₀ • p.up FS FT x := fun x =>
    map_nsmul (GlobalTheory.LocMod.Witness.upH p FS FT) k₀ x
  let f : Matrix Y Y' k → ℂ := fun x => Φ (p.up FS FT x)
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hV : IsOpen {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} :=
      hAo.preimage (continuous_const_smul _)
    have h0 : (x - x) ∈ {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} := by
      simp only [sub_self, Set.mem_setOf_eq, smul_zero]; exact A.zero_mem
    have hn := (continuous_sub_right x).continuousAt.preimage_mem_nhds (hV.mem_nhds h0)
    filter_upwards [hn] with y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
    have hy' : y = x + k₀ • ((k₀ : k)⁻¹ • (y - x)) := by
      rw [hnsmul, smul_smul, mul_inv_cancel₀ hkk, one_smul, add_sub_cancel]
    show Φ (p.up FS FT y) = Φ (p.up FS FT x)
    rw [hy', GlobalTheory.LocMod.Witness.up_add, hup_nsmul]
    exact hinv _ hy (GlobalTheory.LocMod.Witness.up_half p FS FT _) _
  have hcpt : HasCompactSupport f := by
    refine HasCompactSupport.intro (hAc.image (continuous_const_smul ((k₀ : k)⁻¹))) fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨k₀ • x, ?_, ?_⟩
    · show p.up FS FT (k₀ • x) ∈ Λ
      rw [hup_nsmul]; exact hsup _ hne
    · show (k₀ : k)⁻¹ • k₀ • x = x
      rw [hnsmul, smul_smul, inv_mul_cancel₀ hkk, one_smul]
  refine ⟨⟨f, hloc, hcpt⟩, ?_⟩
  funext t
  rw [GlobalTheory.LocMod.Witness.ext_apply]
  split_ifs with ht
  · show Φ (p.up FS FT (p.down FS FT t)) = Φ t
    rw [GlobalTheory.LocMod.Witness.up_down p FS FT ht]
  · by_contra h
    exact ht (hsupp t (Ne.symm h))

end GlobalTheory.SBOfHalf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzBruhatExtByZeroOfSplitPlaceHalfStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

theorem _root_.GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  first | exact @GlobalTheory.SBOfHalf.exists_sb_ext_eq | exact GlobalTheory.SBOfHalf.exists_sb_ext_eq | (intros; apply GlobalTheory.SBOfHalf.exists_sb_ext_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMulConjugateHalfCharacterSplitPlac

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModSB

theorem continuous_pi_hO_up {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T) :
    Continuous fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y) := by
  have h : (fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y)) = fun t =>
      ∑ a, ∑ b, ∑ c, ∑ d, p.π (incA D (S.gram⁻¹ a b)) * p.π (cA D (y c b)) * p.π (incA D (T.gram c d)) *
        (FT.β * t * FS.γ) d a := by
    funext t
    unfold hO

    simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [GlobalTheory.LocMod.Place.up, Matrix.map_apply, p.π_ι]
  rw [h]
  have hm : Continuous fun t : Matrix Y Y' k => FT.β * t * FS.γ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ =>
    continuous_finsetSum _ fun d _ => continuous_const.mul (hm.matrix_elem d a)

theorem mul_char_mem_SB : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T), IsHalf (cA D p.e) y → ∀ Φ ∈ SB (Matrix Y Y' k), (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) ∈ SB (Matrix Y Y' k) := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT y hy Φ hΦ
  obtain ⟨⟨ψk, hk⟩, hc, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  have hcont := (hc ψk hk).1
  have heq : (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) =
      fun t => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ) * Φ t := by
    funext t
    rw [GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hk t y]
  rw [heq]
  have hl : IsLocallyConstant (fun t : Matrix Y Y' k => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ)) :=
    ((GlobalTheory.IrredSB.char_isLocallyConstant ψk hcont).comp_continuous (continuous_pi_hO_up p FS FT y)).comp
      (fun z : Circle => (z : ℂ))
  exact ⟨hl.mul hΦ.1, HasCompactSupport.mul_left hΦ.2⟩

end GlobalTheory.ModSB

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMulConjugateHalfCharacterSplitPlacStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

theorem _root_.GlobalTheory.T.schwartzBruhat_mul_conjugateHalf_character_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T), IsHalf (cA D p.e) y → ∀ Φ ∈ SB (Matrix Y Y' k), (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) ∈ SB (Matrix Y Y' k) := by
  first | exact @GlobalTheory.ModSB.mul_char_mem_SB | exact GlobalTheory.ModSB.mul_char_mem_SB | (intros; apply GlobalTheory.ModSB.mul_char_mem_SB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHomLatticeCompletionOpenCompact

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.OpenCompactLat

theorem isOpen_isCompact_of_nsmul {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {Y Y' : Type}
    (A A₀ : AddSubgroup (Matrix Y Y' k)) (ho : IsOpen (A₀ : Set (Matrix Y Y' k)))
    (hc : IsCompact (A₀ : Set (Matrix Y Y' k))) (M N : ℕ) (hM : (M : k) ≠ 0) (hN : (N : k) ≠ 0)
    (h1 : ∀ x ∈ A, M • x ∈ A₀) (h2 : ∀ y ∈ A₀, N • y ∈ A) :
    IsOpen (A : Set (Matrix Y Y' k)) ∧ IsCompact (A : Set (Matrix Y Y' k)) := by
  have hU : IsOpen ((fun x : Matrix Y Y' k => (N : k) • x) '' (A₀ : Set (Matrix Y Y' k))) :=
    (Homeomorph.smulOfNeZero (N : k) hN).isOpenMap _ ho
  have hA : IsOpen (A : Set (Matrix Y Y' k)) := by
    refine A.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds ⟨0, A₀.zero_mem, smul_zero _⟩) ?_)
    rintro _ ⟨y, hy, rfl⟩
    change (N : k) • y ∈ A
    rw [Nat.cast_smul_eq_nsmul]
    exact h2 y hy
  refine ⟨hA, IsCompact.of_isClosed_subset (hc.image (continuous_const_smul ((M : k)⁻¹))) (A.isClosed_of_isOpen hA) ?_⟩
  intro x hx
  refine ⟨M • x, h1 x hx, ?_⟩
  change (M : k)⁻¹ • (M • x) = x
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hM, one_smul]

theorem openCompact : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T), Submodule.IsFullLattice D.host.E LS → Submodule.IsFullLattice D.host.E LT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), IsOpen (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) ∧ IsCompact (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) := by
  intro D k _ _ _ _ p S T LS LT hLS hLT Y Y' _ _ _ _ FS FT
  have hF := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hG := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  letI := hLS
  letI := hLT
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hF
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hG
  obtain ⟨M, hM, hM'⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO
    (ΛS' := GlobalTheory.PlaceModel.latFrame S) (ΛT' := GlobalTheory.PlaceModel.latFrame T)
    hLS.toIsLattice.fg hLT.toIsLattice.fg inferInstance inferInstance
  obtain ⟨N, hN, hN'⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (ΛS' := LS) (ΛT' := LT)
    hF.1.fg hG.1.fg inferInstance inferInstance
  have hcast : ∀ n : ℕ, 0 < n → (n : k) ≠ 0 := fun n hn => by
    have h0 : IsUnit (n : D.host.E) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    have h1 := (h0.map (incA D)).map p.pr
    rw [map_natCast, map_natCast] at h1
    exact h1.ne_zero
  refine isOpen_isCompact_of_nsmul _ _ (GlobalTheory.LocMod.Witness.lat_open (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT hF hG)
    (GlobalTheory.LocMod.Witness.lat_compact (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT hF hG) M N (hcast M hM) (hcast N hN) ?_ ?_
  · intro x hx
    rw [AddSubgroup.mem_comap] at hx ⊢
    rw [map_nsmul]
    exact hM' _ (GlobalTheory.PlaceModel.latO_le_top _ hx)
  · intro y hy
    rw [AddSubgroup.mem_comap] at hy ⊢
    refine GlobalTheory.SplitLinAt.latHalf D k p S T LS LT _ ?_ (Or.inl ?_)
    · rw [map_nsmul]
      exact hN' _ hy
    · exact GlobalTheory.LocMod.Witness.up_half (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT _

end GlobalTheory.OpenCompactLat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHomLatticeCompletionOpenCompactStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

theorem _root_.GlobalTheory.T.splitPlace_homLattice_completion_openCompact : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T), Submodule.IsFullLattice D.host.E LS → Submodule.IsFullLattice D.host.E LT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), IsOpen (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) ∧ IsCompact (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) := by
  intro D k _ _ _ _ p S T LS LT hLS hLT
  letI := hLS
  letI := hLT
  exact GlobalTheory.OpenCompactLat.openCompact D k p S T LS LT inferInstance inferInstance
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceModelExtensionLineLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModelExtend

theorem isFullLattice_span {D : D7} {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    Submodule.IsFullLattice D.host.E (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
  have hζ : ζ ≠ 0 := by
    rintro rfl
    exact h.2 (by simp)
  letI : Submodule.IsLattice D.host.E
      (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) :=
    Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span_singleton ζ)
  refine ⟨?_⟩
  rw [Submodule.span_span_of_tower]
  exact (finrank_eq_one_iff_of_ne_zero ζ hζ).1 (by rw [Module.finrank_fin_fun, h.1])


open GlobalTheory.LocMod in
theorem exists_placeModel_ext : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S L'' : HSp D) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : GlobalTheory.LocMod.Frame k S.rank n) (FL'' : GlobalTheory.LocMod.Frame k L''.rank Unit) (TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ)), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FS FL'' TL → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ ∀ Φ, T₃ (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FS FL'' Φ) = TL Φ := by
  intro D k _ _ _ _ p ψ hψ hU S L'' ζ₀ hζ LS hLS n _ _ FS FL'' TL hTL
  classical
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set Λ := latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v) with hΛ
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S LS hLS
  letI := isFullLattice_span hζ
  obtain ⟨hAo, hAc⟩ := GlobalTheory.T.splitPlace_homLattice_completion_openCompact D k p S L'' LS
    (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀}) inferInstance inferInstance Unit n FS FL''
  have hinj : Function.Injective (Witness.ext P FS FL'') := by
    intro Φ Ψ h
    apply Subtype.ext; funext x
    have := congrFun h (P.up FS FL'' x)
    rwa [Witness.ext_apply, Witness.ext_apply, if_pos (Witness.up_half P FS FL'' x),
      if_pos (Witness.up_half P FS FL'' x), Witness.down_up] at this
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Witness.ext P FS FL'') (LinearMap.ker_eq_bot.2 hinj)
  set T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ) := TL ∘ₗ G with hT₃d
  have hT₃ : ∀ Φ, T₃ (Witness.ext P FS FL'' Φ) = TL Φ := fun Φ => by
    change TL (G (Witness.ext P FS FL'' Φ)) = TL Φ
    rw [← LinearMap.comp_apply G, hG, LinearMap.id_apply]
  have hsb : ∀ Φ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Unit n k), Witness.ext P FS FL'' Φ' = Φ :=
    GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf D k P S L'' Unit n FS FL'' Λ hAo hAc
  generalize hA : (Λ.comap (Witness.upH P FS FL'') : AddSubgroup (Matrix Unit n k)) = A at hAo hAc
  have hcl : IsClopen (A : Set (Matrix Unit n k)) := ⟨A.isClosed_of_isOpen hAo, hAo⟩
  let Φ₀ : SB (Matrix Unit n k) := ⟨(A : Set (Matrix Unit n k)).indicator 1,
    (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩
  have e1 : Witness.ext P FS FL'' Φ₀ = halfInd p.e Λ := by
    funext t
    rw [Witness.ext_apply, halfInd]
    change (if IsHalf p.e t then _ else _) = _
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      change (A : Set (Matrix Unit n k)).indicator 1 _ = _
      rw [Set.indicator_apply, ← hA]
      refine if_congr ?_ rfl rfl
      change P.up FS FL'' (P.down FS FL'' t) ∈ Λ ↔ _
      rw [Witness.up_down P FS FL'' ht, and_iff_left ht]
    · rw [if_neg ht, if_neg fun h => ht h.2]
  refine ⟨TL Φ₀, T₃, hTL.theta Φ₀, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, hT₃⟩
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => Φ'.1 (s + P.down FS FL'' x),
      Φ'.2.1.comp_continuous (continuous_add_const _), Φ'.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
    have e2 : (fun t => Witness.ext P FS FL'' Φ' (t + x)) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply, Witness.down_add]
      exact if_congr (Witness.half_add hx) rfl rfl
    rw [e2, hT₃, hT₃, hTL.trans (P.down FS FL'' x) Φ' Φ'' (fun t => rfl), Witness.up_down P FS FL'' hx]
  · obtain ⟨Φ', rfl⟩ := hsb Φ hΦ
    let Φ'' : SB (Matrix Unit n k) := ⟨fun s => ψ (symplO S L'' (P.up FS FL'' s) y) * Φ'.1 s,
      GlobalTheory.T.schwartzBruhat_mul_conjugateHalf_character_splitPlace D k P ψ hψ S L'' Unit n FS FL'' y hy Φ'.1 Φ'.2⟩
    have e2 : (fun t => ψ (symplO S L'' t y) * Witness.ext P FS FL'' Φ' t) = Witness.ext P FS FL'' Φ'' := by
      funext t
      rw [Witness.ext_apply, Witness.ext_apply]
      split_ifs with ht
      · change _ = ψ (symplO S L'' (P.up FS FL'' (P.down FS FL'' t)) y) * _
        rw [Witness.up_down P FS FL'' ht]
      · rw [mul_zero]
    rw [e2, hT₃, hT₃, hTL.modul y hy Φ' Φ'' (fun t => rfl)]
  · rw [one_smul, ← e1, hT₃]

end GlobalTheory.ModelExtend
end
end
end

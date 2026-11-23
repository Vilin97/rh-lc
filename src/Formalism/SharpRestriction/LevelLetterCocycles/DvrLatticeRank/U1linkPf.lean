module

public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionHypothesis
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Imports
public import Formalism.SharpRestriction.LevelLetterCocycles.DdRFull
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalFiltrationHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftFrame
public import Formalism.SharpRestriction.LevelLetterCocycles.LamPS
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.KapPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfG
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3downPfFildRConst
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LevelValueSmul
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfD
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftFiltration

section

@[expose] public section

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem universal_lift_filtration (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
    (S η m : ℕ) (upτ : Bool) (bτ : ℕ)
    (hj : JumpsInV ((D.loc l).PD K) T.ρ τ (deep upτ bτ S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bτ)
    (hm : ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV ((D.loc l).PD K) T.ρ τ a ≤ m) :
    (upτ = true →
      (∀ i : ℤ, i < -((bτ : ℤ) + S) → ∀ d : Fin r → ↥LL.1,
        Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-i) → d = 0) ∧
      r ≤ finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ bτ).comap (Phi ((HW l).W K 1 LL hG) T c ζ rep)) + m) ∧
    (upτ = false →
      finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-(bτ : ℤ) + 1)).comap
        (Phi ((HW l).W K 1 LL hG) T c ζ rep)) ≤ m ∧
      ∀ d : Fin r → ↥LL.1,
        Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-((bτ : ℤ) + S))) := by
  exact UniversalFiltration.universal_filtration_holds D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep
    S η m upτ bτ hj hηb hm

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftRingMembership

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries


open Formalism.MainNotions.N.Ln34.ModelFPf in
theorem universal_lift_ring_membership (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ ∧ π' ∈ ((HW l).W K 1 LL hG).AΔ ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
    ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
    (∃ uE ∈ ((HW l).W K 1 LL hG).AΔ, ∃ uE' ∈ ((HW l).W K 1 LL hG).AΔ, uE' * uE = 1 ∧
      ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = uE * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') ∧
    (∃ uπ ∈ ((HW l).W K 1 LL hG).AΔ, ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' = π' * uπ) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hp9
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  have hπu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE π') := by
    rw [hw0, map_mul, map_pow]
    exact (w0.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  have hEu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
    have hq := Formalism.MainNotions.LiftingTheory.liftb_q_unit ((HW l).W K 1 LL hG)
    rw [hw, map_mul] at hq
    exact isUnit_of_mul_isUnit_right hq
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  have hnzπ : ∀ a : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)), a * π' = 0 → a = 0 := by
    intro a ha
    apply ((HW l).W K 1 LL hG).EE_inj
    have h1 := congrArg (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE) ha
    rw [map_mul, map_zero] at h1
    rw [map_zero]
    exact hπu.mul_left_eq_zero.1 h1
  have hγπ : ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' =
      (1 + (w2 : LetA _ _) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') * π' := by
    rw [sub_eq_iff_eq_add] at hw2
    rw [hw2]
    ring
  exact ⟨hEΔ, hπΔ, hEu, hπu, ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl),
    ⟨u, huΔ, _, hu'Δ, hu.val_inv_mul, hγ⟩,
    ⟨_, u_mem_AΔ ((HW l).W K 1 LL hG) hπΔ hnzπ hγπ, by rw [hγπ]; ring⟩⟩

theorem universal_lift_points (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) = 0 ∧
    coeff 1 (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) ≠ 0 ∧
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ π') ≠ 0 ∧
    ∀ a, ((HW l).W K 1 LL hG).lev c ζ (((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam a) =
      rescale (algebraMap ↥(OL LL) ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.uU ((HW l).W K 1 LL hG) : (↥(OL LL))ˣ) : ↥(OL LL)))
        (((HW l).W K 1 LL hG).lev c ζ a) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hζ : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    rw [hp]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  obtain ⟨-, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, -, -⟩ := hp9
  obtain ⟨e₁, he₁, he₁0⟩ :=
    DescentValuation.u3downPf_lev_E ((HW l).W K 1 LL hG) c ζ hζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') w hw
  refine ⟨?_, ?_, DescentValuation.u3downPf_cc_π' ((HW l).W K 1 LL hG) c ζ hζ π' (sK l K) w0 hw0, ?_⟩
  · rw [he₁]
    simp
  · rw [he₁, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact he₁0
  · intro a
    have hg := ((HW l).W K 1 LL hG).gam_gen
    exact ((Cm l).C K 1 LL hG).tie.lev_Γ _ c ζ ζ 1 1 (by rw [pow_one]; exact hζ)
      (le_of_eq (by simpa [hs] using hg.symm)) (pow_one ζ).symm a

theorem embeddings_card_le_degree (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ τs : Finset (↥K.1 →ₐ[ℚ_[l]] ↥LL.1), (∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → τ ∈ τs) ∧
      τs.card ≤ finrank ↥(K0 K) ↥K.1 := by
  classical
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    apply Nat.finite_of_card_ne_zero
    rw [GenPf.natCard_emb K LL hG]
    exact (Module.finrank_pos (R := ℚ_[l]) (M := ↥K.1)).ne'
  haveI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  haveI : FiniteDimensional ↥(K0 K) ↥K.1 := Module.Finite.right ℚ_[l] ↥(K0 K) ↥K.1
  refine ⟨Finset.univ.filter (fun τ => Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c),
    fun τ ζ hpt => Finset.mem_filter.2 ⟨Finset.mem_univ _, u3upPf_pt_over D HW hG c ζ τ hpt⟩, ?_⟩
  have h := kapPiPf_card ((HW l).W K 1 LL hG) c
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U1r2Basis

section

@[expose] public section

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem u1r2_pt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    LevelExpansions.V.PtHyp (W := (HW l).W K 1 LL hG) T c ζ := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hz : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    rw [hpl]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  obtain ⟨hQ0, hQ1⟩ := framepf_Q_at ((HW l).W K 1 LL hG) hs c ζ hz
  obtain ⟨-, -, -, p4, -⟩ := hA l K 1 LL hG
  have hone : ∃ j : ℕ, IsPrimitiveRoot (1 : ↥LL.1) (((D.loc l).PD K).p ^ j) := ⟨0, by simp⟩
  have hπ1 : ∀ i, PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev i 1 letπ) = 0 := fun i => by
    rw [CrystallineExponents.cc_lev_pi _ i 1 hone, sub_self]
  have hX : ((HW l).W K 1 LL hG).X = letπ := by simp [LocWach.X, hs]
  refine ⟨hT, ⟨1, by simpa using hz⟩, hz.pow_eq_one, hQ0, hQ1, fun x k hk => ?_,
    fun x hx => ((HW l).W K 1 LL hG).N_φ T x hx⟩
  exact (((p4 T hT).1 (c - 1) 1 ⟨0, one_pow _⟩ (by rw [hX]; exact hπ1 _)).1 x k).2 hk

theorem u1r2_basis (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
      (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)), ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k) := by
  classical
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have p9 := (hA l K 1 LL hG).2.2.2.2.2.2.2.2.1
  have h92 := (p9 T hT hs hp2).2.1
  obtain ⟨π₀, E₀, -, hm⟩ := h92
  obtain ⟨⟨r, b, hbΔ, hbu, hbe⟩, -⟩ := hm
  have hw := hp9.2.2.1
  obtain ⟨w₁, hw₁⟩ := hw
  have hs1 : 1 ≤ sK l K := DescentValuation.u3downPf_sK_pos hl K LL hG
  have hBL := MQ.basis_L ((HW l).W K 1 LL hG) T π' (sK l K) hs1 w₁ hw₁ hp9.2.1 b hbΔ hbu hbe c
  obtain ⟨bL⟩ := hBL
  have hsurj : ∀ k, ∃ y : ((HW l).W K 1 LL hG).DD T, ∃ hy : y ∈ NcS ((HW l).W K 1 LL hG) T (c - 1),
      bL k = mkL ((HW l).W K 1 LL hG) T π' c y hy := by
    intro k
    have hq := Submodule.Quotient.mk_surjective _ (bL k)
    obtain ⟨⟨y, hy⟩, hyk⟩ := hq
    exact ⟨y, hy, hyk.symm⟩
  choose rep hrep hbr using hsurj
  exact ⟨r, bL, rep, hrep, hbr⟩

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftValuationPoints

section

@[expose] public section

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem universal_lift_basis (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
      (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)), ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k) := by
  exact u1r2_basis D HW F Cm hA hl K LL hG π' E hp9 T hT c

theorem universal_lift_valuation (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    (∀ x y, x ∈ NcS ((HW l).W K 1 LL hG) T (c - 1) → y ∈ NcS ((HW l).W K 1 LL hG) T (c - 1) →
      valAt ((HW l).W K 1 LL hG) T c ζ (x + y) = valAt ((HW l).W K 1 LL hG) T c ζ x + valAt ((HW l).W K 1 LL hG) T c ζ y) ∧
    (∀ (a : ↥(OL LL)) x, x ∈ NcS ((HW l).W K 1 LL hG) T (c - 1) →
      valAt ((HW l).W K 1 LL hG) T c ζ (a • x) = algebraMap ↥(OL LL) ↥LL.1 a • valAt ((HW l).W K 1 LL hG) T c ζ x) := by
  have hP := u1r2_pt D HW F Cm hA K LL hG T hT c τ ζ hpt
  exact ⟨fun x y hx hy => (LevelExpansions.V.valL ((Cm l).C K 1 LL hG).tie T hP).map_add ⟨x, hx⟩ ⟨y, hy⟩,
    fun a x hx => (LevelExpansions.V.valL ((Cm l).C K 1 LL hG).tie T hP).map_smul a ⟨x, hx⟩⟩

theorem universal_lift_valuation_points (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ ζ' : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) (hpt' : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ' τ)
    (x : ((HW l).W K 1 LL hG).DD T) (hx : x ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) :
    valAt ((HW l).W K 1 LL hG) T c ζ x = valAt ((HW l).W K 1 LL hG) T c ζ' x := by
  have hP := u1r2_pt D HW F Cm hA K LL hG T hT c τ ζ hpt
  have hP' := u1r2_pt D HW F Cm hA K LL hG T hT c τ ζ' hpt'
  have hxN := ((mem_NcS _ T (c - 1) x).1 hx).1
  exact (LevelExpansions.V.valAt_eq ((Cm l).C K 1 LL hG).tie T hP ⟨x, hxN⟩).trans
    (LevelExpansions.V.valAt_eq ((Cm l).C K 1 LL hG).tie T hP' ⟨x, hxN⟩).symm

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U1linkPf

section

@[expose] public section

noncomputable section



namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules


theorem u1link_pf : FirstFrameOfModels := by
  intro D HW F Cm hA hdR hDi hML hMF
  intro l _ hl K LL hG π' E hp9 T₁ T₂ Fm S η m h' up b c α β hIF hHyp
  have hc2 := hHyp.2.1
  have hj2 := hHyp.2.2.2.2.1
  have hηb := hHyp.2.2.2.2.2.1
  have hbS := hHyp.2.2.2.2.2.2.1
  have hh' := hHyp.2.2.2.2.2.2.2.1
  have hm := hHyp.2.2.2.2.2.2.2.2.1
  have hjI : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro τ a ha
    have hd := hj2 τ a ha
    have hb := hbS τ
    have hη := hηb τ
    rw [Set.mem_Icc]
    rcases hd with hd | hd
    · unfold deep at hd
      split_ifs at hd <;> (rw [Set.mem_Icc] at hd; constructor <;> omega)
    · rw [Set.mem_Icc] at hd
      constructor <;> omega
  have hM := u3upPf_MK_pos hl K LL hG h' hh'
  have hMF2 := hMF l hl K LL hG π' E hp9 h' hh' c α β hIF T₂ hc2 hjI
  have hML2 := hML l hl K LL hG π' E hp9 h' hh' T₂ hc2 hjI c
  have hR := UniversalLiftFrames.universal_lift_ring_membership D HW F Cm hA hl K LL hG π' E hp9
  have hT := UniversalLiftFrames.embeddings_card_le_degree D HW K LL hG c
  have hτs := hT.choose_spec.1
  have hcard := hT.choose_spec.2
  have hB := UniversalLiftFrames.universal_lift_basis D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c
  have hrep := hB.choose_spec.choose_spec.choose_spec.choose
  have hbrep := hB.choose_spec.choose_spec.choose_spec.choose_spec
  refine UniversalLiftFrames.universal_lift_frame (W := (HW l).W K 1 LL hG) (PD := (D.loc l).PD K) (GenPf.isDVR (D.loc l) LL)
    (GenPf.isFractionRing LL) Fm (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π'
    (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c S η m up b α β hIF hc2 hjI hMF2 hML2 hM
    hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2.1 hR.2.2.2.2.2.2 hT.choose hτs hcard ?_ ?_ hbS ?_ ?_ ?_ hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep ?_ ?_ ?_ ?_ ?_ ?_ ?_ hHyp
  · exact fun τ ζ hpt => u3upPf_pt_over D HW hG c ζ τ hpt
  · exact fun τ => Nat.lt_of_le_of_lt (Nat.zero_le _) (hηb τ)
  · exact fun τ ζ hpt => ⟨(UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).1,
      (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.1⟩
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.2.1
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.2.2
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_valuation D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt).1
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_valuation D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt).2
  · exact fun τ ζ ζ' hpt hpt' k => UniversalLiftFrames.universal_lift_valuation_points D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ ζ' hpt hpt'
      (hB.choose_spec.choose_spec.choose k) (hrep k)
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).1 hup).1
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).1 hup).2
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).2 hup).1
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).2 hup).2

end Formalism.MainNotions.N.Ln34
end
end
end

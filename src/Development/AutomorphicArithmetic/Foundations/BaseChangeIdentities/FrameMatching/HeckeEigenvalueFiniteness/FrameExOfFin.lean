module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.KUEqKLOfNotMemBad
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.HkConstMul
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MapSplit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset
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
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MuVal
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebraStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebraStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryModelHoldsStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.BcWeyl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertEigenvalues.EigInert
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.FrameInertAll
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.SumPairSignEqRho
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CandSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CompFixSAlt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSec
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IsHeckeFsum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.SatCompAt
import GroundTheory.LocalFields.PadicLogSeries

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Mok0

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

theorem mok0 {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) : MLM.MOk F₀.d₀ := by
  have h0 : ∀ w, w ∉ F₀.d₀.T := fun w => by rw [F₀.T₀]; exact Finset.notMem_empty w
  have hlev : ∀ w ∈ F₀.d₀.Bad, GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) (F₀.d₀.KB w) := fun w hw => by
    have h := F₀.levFam.1 w
    have e : F₀.d₀.KU w = F₀.d₀.KB w :=
      (if_neg (h0 w)).trans ((if_neg fun h' => Finset.disjoint_left.1 F₀.ok₀.disj.2.2 h' hw).trans (if_pos hw))
    rwa [e] at h
  refine ⟨fun w hw => absurd hw (h0 w), fun w hw => ⟨(F₀.S₀ w hw).2, fun g => ?_, F₀.K'_lev w hw⟩,
    fun w hw hs => ⟨hlev w hw, fun a ha => ?_⟩, fun w hw hs => ⟨F₀.kB w, F₀.kB_pos w hw hs, hlev w hw, fun γ => ?_, fun a ha => ?_⟩⟩
  · unfold UL
    rw [if_pos (F₀.S₀ w hw).2]
    exact Subgroup.mem_top g
  · rw [F₀.fix_def a ha w, if_pos hw, if_pos hs]
  · have e : {γ : UL n w | γ.1 ∈ MB.congK n w (F₀.kB w)} =
        (((GlobalTheory.PrincCong.congSub w n (F₀.kB w)).subgroupOf (UL n w) : Subgroup (UL n w)) : Set (UL n w)) :=
      Set.ext fun x => (GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) x.1).symm
    rw [F₀.KB_def w, if_pos hw, if_neg hs, e, Subgroup.closure_eq]
    exact GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) γ.1
  · rw [F₀.fix_def a ha w, if_pos hw, if_neg hs]

end UpperTheory.HeckeLevelFrameExistence

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEig

section

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.HeckeLevelFrameExistence.powEig :
    UpperTheory.HeckeLevelFrameExistence.PowEig := by
  intro E _ _ _ n w σ K' hlev g hg y hy m
  have key : ∀ k : ℕ, IsHecke K' (U.lpow K' g k) ∧ locOp σ K' (U.lpow K' g k) y = y := by
    intro k
    induction k with
    | zero =>
      obtain ⟨-, -, -, -, -, -, h1, h2⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g g hg hg
      refine ⟨h1, ?_⟩
      show locOp σ K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) y = y
      rw [h2]
      rfl
    | succ k ih =>
      obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g _ hg ih.1
      refine ⟨h3, ?_⟩
      show locOp σ K' (lconv g (U.lpow K' g k)) y = y
      rw [h5, Module.End.mul_apply, ih.2, hy]
  exact (key m).2
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PTarget

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.Choice
open scoped Classical


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail

theorem qU_add {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (x y : ℤ) :
    qU w (x + y) = qU w x * qU w y := by
  unfold qU
  split_ifs with h
  · exact zpow_add _ x y
  · exact (mul_one 1).symm

theorem targetAlg : TargetAlg := by
  intro E _ _ _ n w s sg ξ ξa ξb hstd hchi
  have hk : ∀ k : Fin n, chiOf w s ξa ξb k = chiN w ξ k := fun k => congrFun hchi k
  constructor
  · intro i
    have h := hk (s.e (Sum.inl i))
    have he := hstd (s.e (Sum.inl i))
    simp only [chiOf, chiN, Equiv.symm_apply_apply, Sum.elim_inl] at h
    simp only [Equiv.symm_apply_apply, Sum.elim_inl] at he
    rw [he, mul_assoc, ← mul_assoc (qU w _), mul_comm (qU w _) (ξa i), mul_assoc (ξa i),
      ← qU_add] at h
    have hr : rh n ↑(s.e (Sum.inl i)) - rh s.a ↑i + (↑s.a - 1 - 2 * ↑↑i) = rh n ↑(s.e (Sum.inl i)) := by
      simp only [rh]
      ring
    rw [hr, ← mul_assoc] at h
    rw [eq_mul_inv_iff_mul_eq, mul_comm]
    exact mul_right_cancel h
  · intro j
    have h := hk (s.e (Sum.inr j))
    have he := hstd (s.e (Sum.inr j))
    simp only [chiOf, chiN, Equiv.symm_apply_apply, Sum.elim_inr] at h
    simp only [Equiv.symm_apply_apply, Sum.elim_inr] at he
    rw [he, mul_assoc, ← mul_assoc (qU w _), mul_comm (qU w _) (ξb j), mul_assoc (ξb j),
      ← qU_add] at h
    have hr : rh n ↑(s.e (Sum.inr j)) - rh s.b ↑j + (↑s.b - 1 - 2 * ↑↑j) = rh n ↑(s.e (Sum.inr j)) := by
      simp only [rh]
      ring
    rw [hr, ← mul_assoc] at h
    rw [eq_mul_inv_iff_mul_eq, mul_comm]
    exact mul_right_cancel h

theorem monoRes : MonoRes := by
  intro n s sg ξ hξ hsg
  have hn : ∀ k, ‖((ξ k * (sg k)⁻¹ : ℂˣ) : ℂ)‖ = ‖((ξ k : ℂˣ) : ℂ)‖ := fun k => by
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hsg k, inv_one, mul_one]
  constructor
  · intro i j hij
    simp only [hn]
    exact hξ _ _ (s.monoL.monotone hij)
  · intro i j hij
    simp only [hn]
    exact hξ _ _ (s.monoR.monotone hij)

end PositivityTheory.Rg.BcB.F.Tail

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CandIndep

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

theorem candIndep : CandIndep := by
  intro hR E _ _ _ n π S F₀ T' c c' e e' b b' i s₁ s₂ Pa Pb D
  constructor
  · intro h
    exact ⟨h.ctx, h.leaves₁, h.leaves₂, h.inf₁, h.inf₂, h.vec⟩
  · intro h
    exact ⟨h.ctx, h.leaves₁, h.leaves₂, h.inf₁, h.inf₂, h.vec⟩

end PositivityTheory.Rg.BcB.F.FX

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.ExTbOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

theorem exTbOf : ExTbOf := by
  intro hIP hW hIS hR E _ _ _ hE n _ π hπ S F₀ T
  obtain ⟨w₁, -, -, hw₁s, hw₁u⟩ := hIP E hE n π hπ F₀.Sec F₀.hSec ∅
  let T' : Finset (Pl E) := insert w₁ (T.filter fun w => IsUnramU π w ∧ ¬ IsSplitAt w)
  have key : ∀ w ∈ T', ¬ IsSplitAt w ∧ IsUnramU π w := by
    intro w hw
    rcases Finset.mem_insert.1 hw with h | h
    · subst h; exact ⟨hw₁s, hw₁u⟩
    · have h' := (Finset.mem_filter.1 h).2
      exact ⟨h'.2, h'.1⟩
  refine ⟨T', fun w => if h : w ∈ T' ∧ ¬ IsSplitAt w then (hW E hE n w h.2).choose else F₀.d₀.b w,
    ⟨w₁, Finset.mem_insert_self _ _⟩, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hs, hu⟩ := key w hw
    have h : w ∈ T' ∧ ¬ IsSplitAt w := ⟨hw, hs⟩
    refine ⟨hIS E F₀.Sec F₀.hSec w hs, hs, hu, ?_, fun h0 => hs (F₀.S₀ w h0).2, fun h0 => (F₀.bad w h0).2 hs hu⟩
    dsimp only
    rw [dite_eq_left h]
    exact (hW E hE n w h.2).choose_spec
  · intro w hw
    dsimp only
    rw [dite_eq_right (fun h => hw h.1)]
  · intro w hw hu hs
    exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hw, hu, hs⟩)

end PositivityTheory.Rg.BcB.F.FX

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSecAlt

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FX

theorem inertInSec : InertInSec := by
  intro E _ _ _ S hS w hw
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
  by_cases h : u = w
  · exact h ▸ huS
  · exact absurd ⟨u, h, hu⟩ hw

end PositivityTheory.Rg.BcB.F.FX

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameExOfFin

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.FX
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

theorem gcHecke : GcHecke := by
  intro E _ _ _ n w hw b ϖ c
  have hg : gc w b ϖ c = ∑ x ∈ c.support,
      (c x * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)) • fU n w b ϖ (lOf x) := by
    funext γ
    simp only [gc, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hg]
  exact isHecke_fsum _ _ _ _ fun x => GlobalTheory.CompanionTheory.MatchPow.fU_hecke hw b ϖ _ (GlobalTheory.LocFinU.continuous_cj w)

theorem frameEx_of_fin (hUS : USide) (hCF : CandFin) : FrameEx :=
  frameEx_of hUS (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.CompanionTheory.LocHecke.locAlg) (GlobalTheory.T.spectral_trace_of_model_algebra GlobalTheory.T.unitary_model_holds GlobalTheory.CompanionTheory.LocHecke.locAlg)
    GlobalTheory.CompanionTheory.LocHecke.locAlg (exTbOf Inert.frameInert_all.1 Inert.frameInert_all.2.1 inertInSec) Inert.frameInert_all.2.2.2.1
    Inert.frameInert_all.2.2.2.2.1 (coneEigOf eigInert LemB.bcWeyl) satCompAt candIndep hCF
    (fun _ _ _ _ _ _ _ _ _ _ F₀ => mok0 F₀) IndefiniteRowSideFullHecke.coneTwo' gcHecke
    (locC IndefiniteRowSideFullHecke.shufEx' IndefiniteRowSideFullHecke.vResStd' IndefiniteRowSideFullHecke.shufStd' targetAlg monoRes) locE muVal powEig

end UpperTheory.HeckeLevelFrameExistence

end
end
end

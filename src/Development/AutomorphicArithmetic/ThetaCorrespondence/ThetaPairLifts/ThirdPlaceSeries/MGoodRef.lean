module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducible
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.IsPrincipalCongruenceAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfMemSupport
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalOfHypOutside
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeOneOfIsCuspidalMultiProd
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.LevSplit

-- Source module: Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.FixOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.B.fixOne :
    UpperTheory.One.M.B.FixOne := by
  intro L _ _ _ n a S hS s f hf hf0 hfix σ hσ
  obtain ⟨c, T, hc, hci, -⟩ := id hσ
  have hiso : f ∈ NG.isoTyp a.ρ S :=
    (le_sSup (s := {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'})
      ⟨hS, LinearEquiv.refl ℂ S, fun _ _ _ e => e⟩ : S ≤ NG.isoTyp a.ρ S) hf
  have hint : ∀ g ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n),
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun g hg => by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
    exact GlobalTheory.StepData.KOne_le_KO hg
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci
    (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1 hint
    (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    f hiso hf0 (fun κ hκ h => by
      rw [hfix κ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκ).1 (hint _ h)) hκ
        ((GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h)]
      simp)
  rw [Submodule.ne_bot_iff]
  refine ⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩
  have e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h := by
    ext i j
    simp
  have hg := GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)
  have h3 := hu _ hg
  rw [e] at h3
  simpa using h3
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.FixSph

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.B.fixSph :
    UpperTheory.One.M.B.FixSph := by
  intro L _ _ _ n a S hS s f hf hf0 hfix σ hσ
  let J : Subgroup (GAf L n) :=
    { carrier := {κ | κ ∈ Umax L n ∧ ∀ g, f (g * κ) = f g}
      one_mem' := ⟨one_mem _, fun g => by rw [mul_one]⟩
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun g => by rw [← mul_assoc, hy.2, hx.2]⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun g => by
        rw [← hx.2 (g * x⁻¹), inv_mul_cancel_right]⟩ }
  have hAF := hS.1.le hf
  have hlev : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, (1 : J →* ℂˣ) ⟨κ, h⟩ = 1 := by
    obtain ⟨-, N, hN, h⟩ := hAF
    exact ⟨N, hN, fun κ hκ => ⟨⟨hκ.1, h κ hκ⟩, rfl⟩⟩
  have hB : NG.HypOutside J (1 : J →* ℂˣ) {s.v}ᶜ := by
    intro κ hκ
    rw [compl_compl] at hκ
    exact ⟨⟨fun h => h.1, fun h => ⟨h, fun g => congrFun (hfix κ h hκ) g⟩⟩, fun _ => rfl⟩
  have hiso : f ∈ NG.isoTyp a.ρ S :=
    (le_sSup (s := {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'})
      ⟨hS, LinearEquiv.refl ℂ S, fun _ _ _ h => h⟩ : S ≤ _) hf
  have hT : f ∈ NG.TypeSp a.ρ J (1 : J →* ℂˣ) := ⟨hAF, fun κ => by
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact funext κ.2.2⟩
  have h := GlobalTheory.SphHyp.isSpherical_of_hypOutside L n a S hS J 1 hlev _ hB f hiso hT hf0 s (by simp) σ hσ
  exact GlobalTheory.BCOffT.isSpherical_of_equiv (equivRep σ).symm h
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodRef

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M.B

theorem good_of_fix {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W))
    (hS : NG.IsIrrRep a.ρ S) (s : SplitPlace L) {p : Prop}
    (hp : p → ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i) (f : GAf L n → a.W) (hf : f ∈ S)
    (hf0 : f ≠ 0) (hff : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (p → IsPrincipalCongruenceAt s κ) → NG.rt L n κ f = f) (σ) (hσ : IsLocS S s σ) :
    UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ) := by
  by_cases h : p
  · have h1 := fixOne L n a S hS s f hf hf0 (fun κ x y z => hff κ x y fun _ => z) σ hσ
    exact GlobalTheory.AVGood.good_of_fixed_KOne UpperTheory.Zero.LLC.Pr.zel (hp h) _
      (GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm h1)
  · exact GlobalTheory.AVGood.good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz _
      (GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm
        (fixSph L n a S hS s f hf hf0 (fun κ x y => hff κ x y fun z => absurd z h) σ hσ))

end UpperTheory.One.M.B
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MGoodRef

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M.B
end UpperTheory.One.M.B
open UpperTheory.One.M.B in
theorem UpperTheory.One.M.goodRef_alt :
    _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → UpperTheory.One.M.GoodAU (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS) := by
  intro _ hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters
  refine GlobalTheory.LiftRef.overRows_and_mono levSplit levSplit (fun K B f T w Z Wt hX z p0 Y h' _ => ?_)
  intro Rw a M tup Q hMA _ j h1 h2 S hS hne s σ hσ
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, i.1 + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hry : (M _ _ h1 h2).real y ≠ 0 := fun e =>
    hy0 ((M _ _ h1 h2).real_inj (e.trans (map_zero _).symm))
  obtain ⟨f', hf', hf0', hff'⟩ := GlobalTheory.AutUnr.exists_fixed_of_isoTyp _ hS.1.stable
    {κ | κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV ∧ TrivOutside {s.v} κ ∧ (s.v ∈ gPl (w.st Z).toD7 → IsPrincipalCongruenceAt s κ)} hy hry
    (fun κ hκ => GlobalTheory.SphInertRef.rt_real_eq_of_lev hMA i y κ (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).1
      (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).2)
  exact good_of_fix _ S hS s (fun hg => GlobalTheory.SplitTypeCompl.exists_padic_equiv _ s hg) f' hf' hf0'
    (fun κ a b c => hff' κ ⟨a, b, c⟩) σ hσ
end
end
end
end

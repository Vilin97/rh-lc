module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevDefs
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialOfCountZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSpherical
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasFixedOfAlgNormFixedNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import GroundTheory.ProfiniteCohomology.LocalClassFormation.UnramifiedRes
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixedUnr

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end
abbrev _root_.UpperTheory.V.Lev.fixedUnr_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Lev.FixedUnrAlt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedIwahoriNeBotOfTwist

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.IwaFix

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem fixed_iwahori_ne_bot_of_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (s : ℂ)
    (T : (twist ρ (detChar (Fin n) (absPow k s))).Equiv ρ') (h : fixed ρ' (iwahori k (Fin n)) ≠ ⊥) :
    fixed ρ (iwahori k (Fin n)) ≠ ⊥ := by
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨x, rfl⟩ := T.toLinearEquiv.surjective y
  refine (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_, fun hx => h0 (by simp [hx])⟩
  have e := T.toIntertwiningMap.isIntertwining _ _ g x
  have hd : absPow k s (Matrix.GeneralLinearGroup.det g) = 1 := by
    have h1 := GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (iwahori_le_KO k (Fin n) hg)
    ext; simp [absPow, h1]
  rw [twist_apply, detChar_apply, hd, Units.val_one, one_smul] at e
  have hy' := GlobalTheory.Parabolic.mem_fixed.1 hy g hg
  exact T.toLinearEquiv.injective (e.trans hy')

end GlobalTheory.AboveL.IwaFix
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfDvd

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem eq_one_of_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem link {n m : ℕ} (b : WDRep h (Fin m → ℂ)) (μ : Fin n → Weil h →* ℂˣ)
    (hp : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ))) (hN : b.N ≠ 0) :
    ∃ i j, (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h) := by
  have hs := b.semisimple (frob h)
  have htop : ⨆ c, Module.End.eigenspace (b.ρ (frob h)) c = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top (b.ρ (frob h))
    simpa only [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1
  obtain ⟨c, v, hv, hNv⟩ : ∃ c v, v ∈ Module.End.eigenspace (b.ρ (frob h)) c ∧ b.N v ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hN (LinearMap.ker_eq_top.1 (top_le_iff.1 ?_))
    rw [← htop]
    exact iSup_le fun c v hv => hc c v hv
  have hfv : b.ρ (frob h) v = c • v := Module.End.mem_eigenspace_iff.1 hv
  have hv0 : v ≠ 0 := fun e => hNv (by rw [e, map_zero])
  have root : ∀ z u, u ≠ 0 → b.ρ (frob h) u = z • u → ∃ i, z = (μ i (frob h) : ℂ) := fun z u hu e => by
    have h1 : Module.End.HasEigenvalue (b.ρ (frob h)) z :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 e, hu⟩
    have h2 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.1 h1
    rw [hp, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, by simpa [sub_eq_zero] using hi⟩
  have hc2 : b.ρ (frob h) (b.N v) = (((normV w : ℕ) : ℂ) * c) • b.N v := by
    rw [b.comm_apply, deg_frob, zpow_one, hfv, map_smul, smul_smul]
  obtain ⟨j, hj⟩ := root _ _ hv0 hfv
  obtain ⟨i, hi⟩ := root _ _ hNv hc2
  exact ⟨i, j, by rw [← hi, ← hj]⟩
private theorem link_all {n : ℕ} (μ : Fin n → Weil h →* ℂˣ) (hu : ∀ i (s : Ine (F := E) A), μ i (ineIncl h s) = 1)
    {i j : Fin n} (e : (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h)) (s : Weil h) :
    (μ i s : ℂ) = ((normV w : ℕ) : ℂ) ^ deg s * μ j s := by
  obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
  have hv : ∀ k, (μ k s : ℂ) = (μ k (frob h) : ℂ) ^ deg s := fun k => by
    conv_lhs => rw [ht]
    rw [map_mul, map_zpow, hu, mul_one, Units.val_zpow_eq_zpow_val]
  rw [hv, hv, e, mul_zpow]
end
theorem UpperTheory.V.Z.Win.T2.fixedUnr_alt :
    _root_.UpperTheory.V.Lev.fixedUnr_s_ty := by
  intro P F Ω _ _ _ _ _ n w A h rc hrc σ μ hp hu
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  haveI : CharZero (w.adicCompletion F) := algebraRat.charZero _
  have hine : ∀ t : Ine (F := F) A, (rc (algNorm σ)).charPol (ineIncl h t) = (X - C 1) ^ n := fun t => by
    rw [hp]
    simp [hu]
  constructor
  · have hfx : fixed (algNorm σ).rep (iwahori (w.adicCompletion F) (Fin (algNorm σ).1)) ≠ ⊥ := by
      refine UnramSupport.fixed_iwahori_ne_bot P.litN.loc.geo P.litN.loc.zel P.litN.loc.bz _ _ _ _
        (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr fun s hs y hy => ?_
      have hyc : y.IsCusp := hs.isCusp hy
      obtain ⟨m, b, hb, hirr⟩ := id ((H.cusp y).1 hyc)
      have hN : b.N = 0 := by
        have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne F Ω A w h (rc y) ((H.cusp y).1 hyc)
        rwa [← hb, WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
      have hI : ∀ t : Ine (F := F) A, b.ρ (ineIncl h t) = 1 := fun t => by
        refine eq_one_of_dvd _ (b.semisimple _) (n := n) ?_
        rw [← WD.charPol_mk, hb, ← hine t, H.supp _ s hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol (ineIncl h t)) hy)
      have hunr : (rc y).unr := by
        rw [← hb, WD.unr_mk]
        exact ⟨hN, hI⟩
      exact isUnramChar_of_isCusp_of_isSpherical P.litN.loc.geo P.litN.loc.bz P.litN.loc.zel _ y hyc
        ((H.sph y).2 hunr)
    have hfx' : fixed (IrrGL.of σ.ρ σ.smooth σ.irred).rep (iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ :=
      GlobalTheory.AboveL.IwaFix.fixed_iwahori_ne_bot_of_twist _
        ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _)) hfx
    exact fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm hfx'
  · intro hne
    obtain ⟨m, b, hb⟩ := (rc (algNorm σ)).exists_rep
    have hpb : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ)) := fun s => by
      rw [← WD.charPol_mk, hb]
      exact hp s
    have hN : b.N = 0 := by
      by_contra h0
      obtain ⟨i, j, e⟩ := link b μ hpb h0
      obtain ⟨s, hs⟩ := hne i j
      exact hs (link_all μ hu e s)
    have hunr : (rc (algNorm σ)).unr := by
      rw [← hb, WD.unr_mk]
      refine ⟨hN, fun t => eq_one_of_dvd _ (b.semisimple _) (n := n) ?_⟩
      rw [← WD.charPol_mk, hb, hine t]
    obtain ⟨v, hv0, hv⟩ := UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hunr)
    exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.Parabolic.mem_fixed.2 hv, hv0⟩
end
end
end

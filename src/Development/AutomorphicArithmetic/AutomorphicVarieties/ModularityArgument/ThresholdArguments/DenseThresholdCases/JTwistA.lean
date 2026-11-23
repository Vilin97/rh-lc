module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.PrinTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.HodgeTateFromSandwich
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.AbConv
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SphUntw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdCharIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSphUntw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WJTwist
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.TypeGd

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open GlobalTheory.PRep UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC

open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Desc.W.typeGd :
    UpperTheory.V.Z.Desc.W.TypeGd := by
  intro E Ω _ _ _ _ _ n w A h σ rc hrc χ ⟨b, hb, hN, hχ⟩
  have hm : (rc (algNorm σ)).mono0 := hb ▸ (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN
  have hT : UpperTheory.Zero.LLC.Toral (algNorm σ) := by
    refine UpperTheory.Zero.LLC.abConv E Ω A w h rc hrc (algNorm σ) (fun j : Fin n => (χ j).comp (Weil h).subtype) fun t => ?_
    rw [← hb, WD.charPol_mk, hχ t, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
    rfl
  obtain ⟨a, ha, ε, L⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  obtain ⟨s, hs, hch⟩ := hT
  refine ⟨?_, ?_, hm⟩
  · have hs' := GlobalTheory.LocGL.SupportRing.hasSupport_nu hs (-(((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
    have e : (algNorm σ).nu (-(((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) = IrrGL.of σ.ρ σ.smooth σ.irred := by
      unfold algNorm
      rw [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]
    rw [← e]
    refine ⟨_, hs', fun y hy => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
    exact Or.inl (hch z hz)
  · intro p q
    have h1 : ∀ y ∈ s, (rc y).charPol ⁅p, q⁆ = X - 1 := fun y hy => by
      obtain ⟨θ, hθ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y (hch y hy)
      rw [L.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
      have hc1 : ⁅θ (a p), θ (a q)⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm _ _
      simp [hc1]
    have hc : Multiset.card s = (algNorm σ).1 := by
      have h2 := hs.sum_fst
      rw [Multiset.map_congr rfl hch, Multiset.map_const', Multiset.sum_replicate, Fintype.card_fin] at h2
      simpa using h2
    show WD.charPol _ _ = _
    rw [L.supp _ s hs, L.dim, Multiset.map_congr rfl h1, Multiset.map_const', Multiset.prod_replicate, hc]
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsFull

section

@[expose] public section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Desc.W.principal_series_full_statement : _root_.UpperTheory.V.Z.Desc.W.PsFullAlt := by
  intro P L Ω _ _ _ _ _ l _ ι n w A h a ha τ ω hh ψ ph hs hω hp hinj
  have hv := fun i => ((Loc.ordCharIff P.aut.art h ι a ha (hh i) (ψ i)).2 (ω i) (hω i) (ph i)).1 (hp i)
  have key : ∀ i j, (∀ σ : Ine (F := L) A, ω i (a (ineIncl h σ)) = ω j (a (ineIncl h σ))) → i = j := fun i j e =>
    hinj (MonoidHom.ext fun σ => Units.ext (ι.injective (by rw [hv, hv, e])))
  refine (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient P _ n ω (fun i => (hω i).smooth) fun i j hij => ⟨fun e => hij (key i j fun σ => by rw [e]),
    fun e => hij (key i j fun σ => ?_)⟩).2 _ τ.ρ τ.irred hs
  have h1 := DFunLike.congr_fun (ha.absPow_comp 1) (ineIncl h σ)
  rw [Complex.ofReal_one, MonoidHom.comp_apply, GlobalTheory.WeilDeligne.unrChar_apply, deg_ineIncl] at h1
  rw [e, MonoidHom.mul_apply, h1]
  simp
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JTwistA

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Desc.W.twistOk_of_isJ :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → B.TwistOk J :=
  _root_.UpperTheory.V.Z.Desc.W.jTwist_of_alt typeGd _root_.UpperTheory.V.Z.Desc.W.twist_away_statement _root_.UpperTheory.V.Z.Desc.W.sphUntw_alt ordTw _root_.UpperTheory.V.Z.Desc.W.principal_series_full_statement
end
end
end

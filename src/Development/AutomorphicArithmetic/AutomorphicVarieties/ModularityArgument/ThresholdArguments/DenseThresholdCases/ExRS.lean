module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SstConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TIsoOfFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
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

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.ExistsGaloisRepRankTwoOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.SV

theorem galRS_iso {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {π : TR.CuspSub F n}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRS π ι r wt HT)
    (hs : IsSSRep r') (hi : RepIso r r') : IsGalRS π ι r' wt HT := by
  obtain ⟨p, hp⟩ := id hi
  have hp' : ∀ s, p * r s = r' s * p := fun s => by rw [hp, inv_mul_cancel_right]
  have ew : ∀ (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      wdOf h hw ι r' = wdOf h hw ι r := fun w hw A h =>
    ((isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)).of_conj hw p fun g => hp' _).wdOf_eq hw
  have hc : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := F) A)), r'.comp (Dec (F := F) A).subtype g =
      p * r.comp (Dec (F := F) A).subtype g * p⁻¹ := fun A g => hp g
  refine ⟨continuous_of_iso H.cont hi, hs, H.plain, fun w σ hσ hP => ⟨fun A h rc hrc => ⟨fun hl => ?_, fun O _ _ _ Bw hj g => ?_⟩,
    fun A h O _ _ _ Bw hj => ?_⟩, fun w hw B hB => (H.frob w hw B hB).of_iso hi,
    fun w hw A h m => ew w hw A h ▸ H.ratio w hw A h m, H.weights, H.weights_sym, fun w A h O _ _ _ Bw hj σ hσ hS => ?_⟩
  · exact (((H.loc w σ hσ hP).1 A h rc hrc).1 hl).of_conj hl p fun g => hp' _
  · obtain ⟨a1, a2⟩ := ((H.loc w σ hσ hP).1 A h rc hrc).2 O Bw hj g
    exact ⟨ExLib.isPstAt_conj (Loc.PP l) Bw p (hc A) a1, ExLib.wdAt_conj (Loc.PP l) ι Bw h hj p (hc A) ▸ a2⟩
  · obtain ⟨k1, -, -, k4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l (Loc.PP l) F Ω O _ Bw n _ _ p (hc A)
    obtain ⟨a1, a2⟩ := (H.loc w σ hσ hP).2 A h O Bw hj
    exact ⟨k1 a1, fun τ LL' τ' hτ => k4 τ _ (a2 τ LL' τ' hτ)⟩
  · obtain ⟨-, k2, -, -⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l (Loc.PP l) F Ω O _ Bw n _ _ p (hc A)
    exact k2 (H.crys w A h O Bw hj σ hσ hS)

end UpperTheory.Gal.SV
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS

section

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.Gal.SV
theorem exRS_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → ExRS := by
  intro P F Ω _ _ _ _ _ _ l _ ι n _ hn π χ hreg hpol
  obtain ⟨r, wt, HT, H⟩ := _root_.UpperTheory.Gal.SV.gr2S' P.galR F Ω l ι n hn π χ hreg hpol
  have key := H.frob
  have hsm : GlobalTheory.PRep.IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff
  have : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  refine ⟨r, wt, HT, H, ⟨H.ss, ?_⟩, fun r' hr' ha => galRS_iso H ha.1 ?_⟩
  · filter_upwards [sat_ae_of_smooth (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart hsm fun w =>
      let ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F n π w
      ⟨σ, hiso σ hσ⟩, eventually_not_mem F l] with w ⟨B, hB⟩ hw
    exact ⟨B, hB, key w hw B hB⟩
  · refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P F Ω l ι n r r' H.cont hr' H.ss ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem F l] with w ⟨B, hB, hf⟩ hw
    exact ⟨_, key w hw B hB, hf⟩
end UpperTheory.Gal.SV
end
end
end
end

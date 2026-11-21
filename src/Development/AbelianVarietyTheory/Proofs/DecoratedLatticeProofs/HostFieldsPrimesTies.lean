module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.InducedCmType

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Core.Ht2

theorem host_fields_primes_ties : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : ColIn.Ok I) (hX : B.fields.Ok) (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)), (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.ccK = ⊤ ∧ GL3Theta.InducedCMType (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ∧ GL3Theta.HostFieldConditions (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ∧ B.fields.AbelianUnramifiedExtensionConditions ∧ (seamOf B (TC.cols I l) Z.W Z.V Z.S Z.N Z.G).Ok ∧ (∀ x : B.fields.K, B.embLL (star x) = starRingEnd ℂ (B.embLL x)) ∧ (B.primes X).Ok ∧ (B.primes X).PiGCong ∧ (B.primes X).cond = B.host.QS * B.host.q * B.host.d ∧ (∀ i, (B.primes X).g i = B.host.g i) ∧ B.wts.Ok := by
  intro B X I _ _ l Z
  exact ⟨B.toPre.ccK_top, GlobalTheory.InducedType.restrict_K _, Formalism.MainNotions.GL3Theta.cm_field_facts_hold _, (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1,
    seamOf_ok B (TC.cols I l) Z.W Z.V Z.S Z.N Z.G, B.starLL_cx, (GlobalTheory.BasePrimes.primes_ok B X).1, (GlobalTheory.BasePrimes.primes_ok B X).2,
    rfl, fun _ => rfl, B.wts_isOk⟩

end GlobalTheory.Core.Ht2

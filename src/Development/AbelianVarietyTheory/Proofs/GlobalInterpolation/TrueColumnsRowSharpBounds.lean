module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SharpBoundStabilityLatticeColumnChain
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ColumnWeightTwisted
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupleChainSharpColumnValuationOfTwisted
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FivePointLawsTrueChainsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainInitialLatticeCompatibleTrueColumnsStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section
namespace GlobalTheory.LvT.Built.TrueCols

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem trueColumns_chain_last_step_sharp_bound (h : I.Ok) (hJ : I.JetsIn) (hS : GlobalTheory.LvT.WtSign.BaseSigns B) (l : I.Laws) (l0 : I.Law0 l)
    (Z : TC.Later B (I.cols l)) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : I.ι) : Conclusion5Sharp (tw (I.tw l l0 Z) u a) := by
  obtain ⟨Bd, hch, hsp, hse, hk, hBd⟩ := GlobalTheory.T.fivePointLaws_trueChains B X I h hJ l l0 Z u a
  have hT : Module.finrank ℚ Bd.E * (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m + 1 < Bd.J.T := by
    subst hBd
    show Module.finrank ℚ B.host.E * B.R.N B.R.m + 1 < B.T u
    have h1 := X.a_gt
    have h2 := X.T_gt u
    have hf : Module.finrank ℚ B.host.E = 2 * B.R.f := by
      rw [B.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    rw [hf]
    have h3 : ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) < (B.T u : ℝ) := lt_trans h1 h2
    exact_mod_cast h3
  have hW : TwColumn.WtSigns Bd.ch :=
    (GlobalTheory.LvT.WtSign.wtSigns_assemble_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G u Bd.ch).2 hS
  have := (GlobalTheory.LvT.Built.Assemble.sharpBound_stability_latticeColumnChain (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u Bd hsp hse hk hT hW).1
  rwa [hch] at this

theorem row_true : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → GlobalTheory.LvT.WtSign.BaseSigns B →
    ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (Dx : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word),
      Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u ∧ ∀ w : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.places.Pl,
        (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.places.resChar w = ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).mem u).A.T → ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) μ →
        μ ≠ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.mu0 → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u w,
        Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw (I.tw l l0 Z) u μ w x (-(((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m : ℝ) * EatT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u w)) := by
  intro B X I h hJ hS l l0 Z Dx u
  refine ⟨?_, fun w hw μ _ _ _ x hx => ?_⟩
  · have h0 := trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u I.mu0
    rw [← own_eq I l l0 Z u] at h0
    exact (levelChainSharpColumnValuation_ownChain_iff (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u).1 h0
  · have hTw : TupleChainSharpColumnValuation (I.tw l l0 Z) u μ :=
      TwSharp.tupleChainSharpColumnValuation_of_twisted (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u (I.tw l l0 Z) μ (GlobalTheory.T.twistedChain_initialLattice_compatible_trueColumns B X I h l l0 Z u μ)
        (trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u μ)
    exact GlobalTheory.Proof.ColumnWeightTwisted.colGeTw_of_tupleChainSharpColumnValuation (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.tw l l0 Z) u μ hTw w hw x hx

end GlobalTheory.LvT.Built.TrueCols

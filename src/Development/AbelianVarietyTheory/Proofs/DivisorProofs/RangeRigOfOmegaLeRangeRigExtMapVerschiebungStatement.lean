module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRigOfOmegaLeRangeRigExtMapVerschiebung
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung' : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), LinearMap.range (frobTwist h G).rigOfOmega ≤ LinearMap.range (rigExtMap (verschiebung h G)) := by
  first | exact @GlobalTheory.PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung | exact GlobalTheory.PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung | (intros; apply GlobalTheory.PDivGroup.range_rigOfOmega_le_range_rigExtMap_verschiebung <;> assumption)

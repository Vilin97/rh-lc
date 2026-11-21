module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), Formalism.L2.Herm.StdTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ∧ gramP (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) = 1 ∧ (∀ x j, iXc (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) ∧ ∀ i (hi : i ≤ B.R.m), gramN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi = 1 ∧ (∀ x, x ∈ selfDualLatticeCoords (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi ↔ ∀ j, x j ∈ (algebraMap (𝓞 B.host.E) B.host.E).range) ∧ ∀ u a, (∀ c, latCrd (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi (I.latAt u a i c) = ((I.stp u a i).rep c).1.1.deco.1.L) ∧ ∃ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi), I.IdY l Z u a i hi eY ∧ ∀ τ z, (I.chain l u a).de i z τ = ((eY z).1 τ).det := by
  first | exact @GlobalTheory.Mem.Col2.TC.spaces_in_coordinates | exact GlobalTheory.Mem.Col2.TC.spaces_in_coordinates | (intros; apply GlobalTheory.Mem.Col2.TC.spaces_in_coordinates <;> assumption)

module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTieRec

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem weightTie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)), DelNat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) → ∀ u : B.Word, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (numDatumOfParameters (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L) (X := B.fields) (Pr := B.primes X) B.wts (plRec (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) u (codeRec L u) := by
  intro B X I _ l Z L hD u
  obtain ⟨n, hn⟩ := hD
  have hfl : ((⌊(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).s.Del⌋₊ : ℕ) : ℚ) = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).s.Del := by rw [hn, Nat.floor_natCast]
  refine ⟨B.wts_isOk, fun z => ?_, fun z => ⟨?_, fun i => ?_⟩⟩
  · exact GlobalTheory.ColumnNormCompare.mem_tops_rec (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) z
  · exact B.wts_isOk.hc_row u _
  · change ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).hcW u (plRec (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) z)).u i = _
    unfold NumDatum.uW
    obtain ⟨i, hi⟩ := i
    have hi' : i < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k := hi
    by_cases h : 1 ≤ i ∧ i + 1 < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k
    · rw [dite_eq_left h]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hk : k < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k - 2 := by omega
      have a := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).s.u_letter u (plRec (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) z) k hk
      have hv := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).hcW_v u (plRec (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) z)
      rw [a, hv, ← hfl]
      rfl
    · rw [dite_eq_right h]
      by_cases h0 : i = 0
      · subst h0
        exact (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).hcW_first u _ hi'
      · have h1 : i = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k - 1 := by omega
        subst h1
        exact (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).hcW_last u _ (by omega)

end GlobalTheory.CoreHt

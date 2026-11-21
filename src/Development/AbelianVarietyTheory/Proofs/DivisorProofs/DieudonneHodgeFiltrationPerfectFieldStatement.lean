module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectField
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_hodgeFiltration_perfectField : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), (∀ x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧ (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ m, G.rigToLie (p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧ Function.Injective G.rigOfOmega := by
  first | exact @GlobalTheory.Dieu.Theory.hodge_filtration | exact GlobalTheory.Dieu.Theory.hodge_filtration | (intros; apply GlobalTheory.Dieu.Theory.hodge_filtration <;> assumption)

module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.WeylLatDual
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualityPadicMinorsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPolynomialEqOfFunctionEqCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalizedWeylLatticeIffDetTwistedEvalStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.IntDualT

theorem mem_locW_iff_prTC_le_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)) (Pl : Examples₂.EntPl (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (Bs : PlaceMatrixFamily (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ ∀ J, ‖prTC Pl O Bs u μ w i c' v' J‖ ≤ 1) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hLF i hi c' z v' hev
  have hfits := nuFits_tgt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i hi
  have hF := canT_of Pl Bs (GlobalTheory.T.toy_entPl_canOnto _ Pl) u μ w i hi c' (secC O u μ (i + 1) v')
  have hspec := canInv_spec (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) w _ (nuD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i) _ hF
  have hS := GlobalTheory.T.weyl_lattice_duality_padic_minors ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.places.resChar w) _ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tau (tauPl (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))
    (Formalism.L2.DIV.tauPl_bijective _) _ (nuD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i) _ hfits.1 hfits.2
    (canInv (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) w _ (nuD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i) (tgtFun Pl Bs u μ w i c' (secC O u μ (i + 1) v')))
  have hpol := GlobalTheory.T.sectionPolynomial_eq_of_function_eq_coefficient I hOk hPins l Z Y.Qp O hStd u μ i hi z v' hev
  rw [GlobalTheory.T.mem_localizedWeylLattice_iff_detTwisted_eval I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hLF i hi c' z]
  have hfun : (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u μ).sDiv i τ)) *
      atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (i + 1))) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL from z.1) y) =
      tgtFun Pl Bs u μ w i c' (secC O u μ (i + 1) v') := by
    funext y
    rw [← hpol]
    rfl
  rw [hfun, ← hspec]
  exact hS.symm

end GlobalTheory.Mem.IntDualT

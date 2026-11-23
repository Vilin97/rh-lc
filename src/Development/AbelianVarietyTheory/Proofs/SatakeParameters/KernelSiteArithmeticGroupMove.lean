module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeMovedLatticeTupleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPtMoveEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLatticeTupleMoveByRationalIsometry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameMatricesEqOfSameComponentStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleMoveScalarPowerOfPStatement
public import Formalism.SharpRestriction.GrowthBounds.DataG
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryAdelicPointGramStepNormOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponentStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumPairEqAdelicDatumTwoPointsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToMatrixCoMulSymm

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteMoveLatticeTupleAtSuccStep

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.MvS

theorem cast_lev {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (c : C.cls i) (c' : C'.cls i) (hc' : c' = castCls h i c) (β : S.Ch) (hβ : S.chOf c = β) (κ : (S.K β).lev.U) :
    ∃ κ' : (St.K (St.chOf c')).lev.U, κ'.1 = κ.1 ∧ (St.K (St.chOf c')).lev.chi κ' = (S.K β).lev.chi κ := by
  subst hSt hc' h hβ
  exact ⟨κ, rfl, rfl⟩



theorem pt_step {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (β : S.Ch) (hC : S.Core e β) (a : S.cmpt β)
    (γ : ((S.charts.gat β).lev a).Γ) (L : G.P.Tup) (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (hg' : ∀ v, ((S.charts.gat β).lev a).smul γ L v = colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x x' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hx : (S.loc β).IsPt a g x.1) (hx' : (S.loc β).IsPt a g' x'.1) :
    ∃ κ : (S.K β).lev.U, x'.1 = GlobalTheory.TwU.ratA D.host.F ((S.loc β).gamI a γ) * x.1 * κ.1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((S.K β).lev.chi κ : ℂˣ) : ℂ) ∧
        algebraMap G.O G.Kf ((((S.charts.gat β).lev a).χ γ : G.Oˣ) : G.O) = e r := by
  obtain ⟨κa, hκa⟩ := awayEx_of hC.good (S.K β).lev hC.gam a γ
  obtain ⟨ra, hra1, hra2⟩ := hC.chi a γ κa hκa
  obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.TwV.Xc.isPt_move_eq _ _ _ _ _ _ (S.loc β) _ _ _ _ (S.K β).lev hC.good hC.int hC.hypP hC.actB hC.bad_p a γ
    (hC.gamU a γ) κa hκa g g' (fun v => (hg' v).symm.trans (PStabEq.smul_colSpan (G := S.charts.gat β) a γ L g hg v)) x x' hx hx'
  refine ⟨κ, hκ1, ra⁻¹, ?_, ?_⟩
  · rw [map_inv₀, hra1, ← Units.val_inv_eq_inv_val]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (eq_inv_of_mul_eq_one_left hκ2).symm
  · rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hra2

end GlobalTheory.TwV.Xc.MvS

namespace GlobalTheory.TwV.Xc



theorem moveBy_succ : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ i (hi : i + 1 ≤ D.R.m) (c : (sysS H X std).Lv.comp (i + 1)) (La : ((sysS H X std).Pj (i + 1)).Tup) (γ : ((sysS H X std).Lv.lev (i + 1) c).Γ), ((sysS H X std).Pj (i + 1)).IsLatTup La → ∃ g κ, MoveBy std J (i + 1) hi c La γ g κ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS i hi c La γ hL
  obtain ⟨⟨β, a⟩, rfl⟩ := (I.at' i hi).st.eC.surjective c
  have hC := H.core i hi β
  have hpt : ∀ L', ((I.at' i hi).st.loc β).IsPt a
      (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) L')
      (J.pt std (i + 1) hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).1 := by
    intro L'
    have h := (Joint.pt_succ_isPt t std J i hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).2
    have key : ∀ (b : Σ β : (I.at' i hi).st.Ch, (I.at' i hi).st.cmpt β), b = ⟨β, a⟩ → ∀ g x, ((I.at' i hi).st.loc b.1).IsPt b.2 g x →
        ((I.at' i hi).st.loc β).IsPt a g x := by
      rintro _ rfl g x h
      exact h
    exact key _ (Equiv.symm_apply_apply _ _) _ _ h
  have hb := Joint.basesAt_span t std J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) hL
  have hb' : ∀ v, (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) =
      colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La)) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
    intro v
    unfold basesAt
    exact Classical.epsilon_spec (p := fun g' : GL (Fin (((sysS H X std).Pj (i + 1)).m + 1)) ((sysS H X std).G.P.Qq v) =>
      (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) = colSpan ((sysS H X std).G.P.W v) (g' : Matrix _ _ _))
      ⟨_, PStabEq.smul_colSpan (G := (I.at' i hi).st.charts.gat β) a γ La _ (fun v => hb v) v⟩
  obtain ⟨κ, hκ, r, hr1, hr2⟩ := MvS.pt_step (I.at' i hi).st _ β hC a γ La _ _ (fun v => hb v) (fun v => hb' v) _ _ (hpt La) (hpt _)
  have hc : (I.at' i hi).st.chOf (clsOf (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La) = β :=
    (clsOf_chart (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La hL).trans
      (congrArg Sigma.fst (Equiv.symm_apply_apply (I.at' i hi).st.eC ⟨β, a⟩))
  obtain ⟨κ', hκ'1, hκ'2⟩ := MvS.cast_lev (X.onCh i hi) (I.at' i hi).st (J.St (i + 1) hi) (J.st i hi) _
    (clsAt X H (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩) La) (clsAt_succ X H i hi _ La) β hc κ
  refine ⟨((I.at' i hi).st.loc β).gamI a γ, κ', hC.gamU a γ, ?_, ?_, r, ?_, hr2⟩
  · exact hκ.trans (congrArg _ hκ'1.symm)
  · intro hr v
    have hB : (J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc β).rk.symm) ((I.at' i hi).st.loc β).B := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).B = _
      rw [dite_eq_left hi]
      show Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).rk.symm)
        ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).B = _
      rw [Equiv.symm_apply_apply]
    have hJ : (J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        (gramN D (i + 1) hi).reindex (finCongr ((I.at' i hi).st.loc β).rk.symm) (finCongr ((I.at' i hi).st.loc β).rk.symm) := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).J = _
      rw [dite_eq_left hi]
    have hiw : (J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) = ((I.at' i hi).st.loc β).iw := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).iw = _
      rw [dite_eq_left hi]
      show ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).iw = _
      rw [Equiv.symm_apply_apply]
    have hρ : J.rho std v = ((I.at' i hi).st.loc β).iw v := (J.iw i hi β v).symm
    have hF : (J.fd std).frM (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v =
        (((LinearMap.toMatrix' ((stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La))).toLinearMap)) *
          ((J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La)).1).map ((J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v)).submatrix
          (finCongr rfl) (finCongr rfl) := rfl
    rw [hF, hB, hJ, hiw, hρ]
    exact Mv0.frm_gen (Q := (sysS H X std).G.P.Qq v) _ ((I.at' i hi).st.loc β).rk hr (gramN D (i + 1) hi) ((I.at' i hi).st.loc β).B (((I.at' i hi).st.loc β).gamI a γ)
      (((I.at' i hi).st.loc β).iw v) _ (hC.actB a v γ)
  · exact hr1.trans (congrArg (fun z : ℂˣ => (z : ℂ)) hκ'2.symm)

end GlobalTheory.TwV.Xc

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteMoveLatticeTupleAtSuccStepStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_move_latticeTuple_at_succStep : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ i (hi : i + 1 ≤ D.R.m) (c : (sysS H X std).Lv.comp (i + 1)) (La : ((sysS H X std).Pj (i + 1)).Tup) (γ : ((sysS H X std).Lv.lev (i + 1) c).Γ), ((sysS H X std).Pj (i + 1)).IsLatTup La → ∃ g κ, MoveBy std J (i + 1) hi c La γ g κ) := by
  first | exact @GlobalTheory.TwV.Xc.moveBy_succ | exact GlobalTheory.TwV.Xc.moveBy_succ | (intros; apply GlobalTheory.TwV.Xc.moveBy_succ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmpFamMemFunMod

section

@[expose] public section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

namespace CmpMem

theorem isLattice_map {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A : GL (Fin k) K)
    {L : Submodule R (Fin k → K)} (hL : IsLattice R L) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) := by
  obtain ⟨g, hg, rfl⟩ := hL
  refine ⟨(A : Matrix (Fin k) (Fin k) K) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul hg
  · unfold colSpan
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf}

theorem isLatTup_smul (C : Level P) (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) :=
  fun v => isLattice_map (C.act v γ) (hL v)

variable {X : Fields} (T : PlTie X P) {n : ℕ} (hn : n = P.m + 1) {lam : X.Tau → DomWeight n} {c : ℤ}

variable {S : GSD X.K} (Y : PSys X n p lam S)

end CmpMem

end GlobalTheory.GO
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumMovedLatticeTuple

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem stdG_one_apply {D : D7} {N : ℕ} (J : Matrix (Fin N) (Fin N) D.host.E) (v : Fin N → D.host.E) :
    stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J 1 v = v := by
  have h : ∀ w : Fin N → D.host.E, toLE (1 : GL (Fin N) D.host.E) w = w := by
    intro w
    simp [toLE, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]
  show (stdCo _ J) (toLE 1 ((stdCo _ J).symm v)) = v
  rw [h, LinearEquiv.apply_symm_apply]

theorem inFr_stdG_homRe {D : D7} {a b N N' : ℕ} (hr : a = N) (hr' : b = N') (J : Matrix (Fin N) (Fin N) D.host.E)
    (J' : Matrix (Fin N') (Fin N') D.host.E) (g : GL (Fin N) D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    Formalism.L2.Col.inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1) (homRe hr hr' x) =
      homRe hr hr' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) J g)) := by
  subst hr hr'
  apply LinearMap.ext
  intro v
  have h1 : ∀ w, (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1).symm w = w := by
    intro w
    rw [LinearEquiv.symm_apply_eq, stdG_one_apply]
  simp only [Formalism.L2.Col.inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, homRe, eMat]
  congr 2
  ext i
  simp [Matrix.toLin'_apply, LinearMap.toMatrix'_mulVec]

end GlobalTheory.TwV.Xc



theorem GlobalTheory.TwV.Xc.xiM_smul_moveBy : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar ∧ ∀ x, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' x = (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, La) La' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLa hM La'
  have hj' : j + 1 ≤ D.R.m := hj
  have hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := (GlobalTheory.TwV.DelB.sysS_ranks S).2.2.1 (j + 1)
  obtain ⟨hg, hpt, -, r, hr0, -⟩ := hM
  have hκU := ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U_eq κ.1).1 κ.2).1

  have hdet : Matrix.GeneralLinearGroup.det κ.1 ∈ U1 (sigD D) := det_unitary_adelic_point_gram_step_norm_one D j hj.le ⟨κ.1, hκU⟩
  refine ⟨?_, fun x => ?_⟩
  · have hmu := S.law.mu_alg j hj _ hdet
    have hchi : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar := by
      rw [← hr0]
      exact (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) r).algHom (D.what₂.embLL.toRatAlgHom))
    exact mul_mem hmu (inv_mem hchi)
  · have e1 := GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj' hr hr' (c, ((sysS H X std).Lv.lev j c).smul γ La) La' x
    have e2 := GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj' hr hr' (c, La) La'
      (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))
    have hch := GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j hj.le c (((sysS H X std).Lv.lev j c).smul γ La) La
      (GlobalTheory.GO.CmpMem.isLatTup_smul _ γ hLa) hLa
    rw [e1, e2, hch]
    have hx0 : (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)).1 * κ.1⁻¹ ∈
        UPts (sigD D) (gramN D j hj.le) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      mul_mem (J.pt std j hj.le _).2 (inv_mem hκU)
    have hlev := S.law.lev j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La')
      (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)) (J.pt std (j + 1) hj' La') κ 1
      (by show _ = _ * _ * _; group) (by simp) (homRe hr hr' x)
    have hrat := S.law.rat j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') (J.pt std j hj.le (c, La))
      (J.pt std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La') g hg 1 (one_mem _)
      (by show _ * _ = _; rw [hpt]; group) (by simp) (homRe hr hr' x)
    rw [inFr_stdG_homRe] at hrat
    rw [hrat] at hlev
    simp only [OneMemClass.coe_one, map_one, (S.law.mu_mul j hj).1, one_mul, Units.val_one, mul_one] at hlev
    have hc : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    linear_combination hlev
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumMovedLatticeTupleStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedDatum_movedLatticeTuple : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar ∧ ∀ x, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' x = (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, La) La' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))) := by
  first | exact @GlobalTheory.TwV.Xc.xiM_smul_moveBy | exact GlobalTheory.TwV.Xc.xiM_smul_moveBy | (intros; apply GlobalTheory.TwV.Xc.xiM_smul_moveBy <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLatticeTupleMoveByRationalIsometryStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_latticeTuple_move_by_rational_isometry : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (c : (sysS H X std).Lv.comp 0) (La : ((sysS H X std).Pj 0).Tup) (γ : ((sysS H X std).Lv.lev 0 c).Γ), ((sysS H X std).Pj 0).IsLatTup La → ∃ g κ, MoveBy std J 0 (Nat.zero_le _) c La γ g κ) := by
  first | exact @GlobalTheory.TwV.Xc.moveBy_zero | exact GlobalTheory.TwV.Xc.moveBy_zero | (intros; apply GlobalTheory.TwV.Xc.moveBy_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMove

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc



theorem site_move : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Move) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  intro j hj c L La' γ hL hLa'
  rw [hmm] at hj
  have hr := hN j
  obtain ⟨g, κ, hM⟩ : ∃ g κ, MoveBy std J j hj.le c L γ g κ := by
    cases j with
    | zero => exact GlobalTheory.T.stepZero_latticeTuple_move_by_rational_isometry S hD hS c L γ hL
    | succ i => exact GlobalTheory.T.kernelSite_move_latticeTuple_at_succStep S hD hS i hj.le c L γ hL
  have hU := ((GlobalTheory.TwV.Xc.eMat_unitary_det _ _ (fun _ => rfl) _ _ hr _ _ (J.pins.crd_orth j hj.le)).2 g hM.1).1
  obtain ⟨hcq, hxi⟩ := GlobalTheory.T.movedDatum_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM La'
  refine ⟨eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g, _, hU, ?_,
    GlobalTheory.T.kernelLattice_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM, hcq, hxi, GlobalTheory.T.latticeTupleMove_scalar_power_of_p S hD hS hPos hPair j hj c L γ g κ hr hL hM La' hLa'⟩
  intro v
  rw [GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hD hS j c (((sysS H X std).Lv.lev j c).smul γ L) L]
  exact hM.2.2.1 hr v

end GlobalTheory.TwV.Xc
end
end

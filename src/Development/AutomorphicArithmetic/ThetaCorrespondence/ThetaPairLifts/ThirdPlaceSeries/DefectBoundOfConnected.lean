module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeSlopeLowerBoundDefiniteCaseStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefCaseCoreStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCore
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeBaseStatement
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatExistsAtCoreStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuLowerBoundLastIndex

section

@[expose] public section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.DefCore

theorem unitE_nonneg {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) : 0 ≤ unitE p := by
  rw [hw.unit]
  have hx : 0 < L.sc.x := by linarith [hh.big.2.1, hh.big.2.2.1]
  have hb : 0 < L.sc.b := lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hx _) _) hh.room
  have := hh.big.2.2.2
  have : (0:ℝ) ≤ L.sc.L := by linarith [hh.big.2.1]
  positivity

end GlobalTheory.CovTop.DefCore

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupLevel

section

@[expose] public section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefEig

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem actLev_levB (p : PtAt ex Csz) (i : Fin D.R.m) :
    ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  have h : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1
  exact ⟨fun g => h.total g, fun g => h.func g, h.one, fun g g' => h.mul g g', fun g => h.nat g, fun g => h.bor g⟩



theorem mem_eigSub_iff (p : PtAt ex Csz) (i : Fin D.R.m) (χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ)
    (f : p.T.R ((i : ℕ) + 1)) :
    f ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      ∀ u : (p.F.lv2.lvl false).P,
        actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f := by
  simp only [eigSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  rfl


end GlobalTheory.DefEig
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigSlopeLe

section

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefEig
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem actKeeps_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') : ActKeeps (κ := p.κ) p.O i := fun g f hf => by
  obtain ⟨cc, ph, hO⟩ := (hp.oneMap i).1
  obtain ⟨k, hk, -⟩ := (p.pins i).2.lift.lev g
  exact (hO.1 g k hk f hf).1
theorem exists_chi_algebraMap_eq_FW_chi_mul_psi_inv (p : PtAt ex Csz) (i : Fin D.R.m) (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) :
    ∃ χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ, ∀ u, algebraMap p.T.Q.c.F D.what₂.LL (χ u : p.T.Q.c.F) =
      (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) := by
  have hv := _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt p i hp.1 hp.2
  choose b hb using hv
  have hinj : Function.Injective (algebraMap p.T.Q.c.F D.what₂.LL) := (algebraMap p.T.Q.c.F D.what₂.LL).injective
  have hb0 : ∀ u, b u ≠ 0 := fun u h => by
    have := hb u
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  refine ⟨{ toFun := fun u => Units.mk0 (b u) (hb0 u), map_one' := ?_, map_mul' := ?_ }, fun u => hb u⟩
  · refine Units.ext (hinj ?_)
    simp [hb]
  · intro u v
    refine Units.ext (hinj ?_)
    simp only [Units.val_mk0, Units.val_mul, map_mul, hb, Subgroup.coe_mul, MonoidHom.inv_apply]
    push_cast
    ring
set_option maxHeartbeats 1000000 in
theorem exists_finite_group_lev_char_slope : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∃ (G : Type) (_ : Group G) (_ : Finite G) (lev : G → ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La) × ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La)) (χ : G →* (p.T.Q.c.F)ˣ), ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ slope_sq (normW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)) (eigLat (p.T.U ((i : ℕ) + 1)) lev χ (Gk p i)) ≤ muCore p i := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hp hi hG hW hH hF
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.DefEig.exists_chi_algebraMap_eq_FW_chi_mul_psi_inv p i hp
  have hK := _root_.GlobalTheory.DefEig.actKeeps_alt p i hp.1
  have hρ := (p.rhoGeo i).1 hK
  have hsm : ∀ (u : (p.F.lv2.lvl false).P) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n),
      ((p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f) : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
        (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
          ((p.fw.e i f : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := fun u f => by
    rw [LinearEquiv.map_smul, Submodule.coe_smul, ← hχ u, algebraMap_smul]
  refine ⟨(p.F.lv2.lvl false).P, inferInstance, inferInstance, fun g => (p.O i).lev2 (g : p.P.Gp), χ, actLev_levB p i,
    _root_.GlobalTheory.T.freePt_last_index_of_fnAlgClosed p i PP A M hp hi hG hW hH hF, le_of_eq ?_⟩
  have hAB : ((eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ).comap
        (cuspW (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.T.U ((i : ℕ) + 1)) (Gk p i)).subtype).restrictScalars (𝓞 p.T.Q.c.F) =
      ((Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)).comap (VK p.fw i).subtype).restrictScalars (𝓞 p.T.Q.c.F) := by
    ext x
    change (x : p.T.R ((i : ℕ) + 1)) ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      (x : p.T.R ((i : ℕ) + 1)) ∈ Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)
    have hx : (x : p.T.R ((i : ℕ) + 1)) ∈ p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n := by
      exact (cuspW_wtZ (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c) (U := p.T.U ((i : ℕ) + 1))
        (wtA (p.κ i)) (p.κ i).n).le x.2
    constructor
    · intro h
      rw [mem_eigSub_iff] at h
      apply Submodule.subset_span
      refine ⟨hx, fun u => ?_⟩
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨x, hx⟩
      rw [← h2]
      have h3 : (⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) (x : p.T.R ((i : ℕ) + 1)), hf'⟩ :
          p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨x, hx⟩ :=
        Subtype.ext (h u)
      exact (congrArg (fun y => ((p.fw.e i y : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL)) h3).trans (hsm u ⟨x, hx⟩)
    · intro h
      refine Submodule.span_le.2 ?_ h
      rintro f ⟨hf, hT⟩
      rw [SetLike.mem_coe, mem_eigSub_iff]
      intro u
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨f, hf⟩
      have h4 : (p.R.FW i).ρ (u : p.P.Gp) ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
          (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
            ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := hT u
      have h5 : (p.fw.e i ⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f, hf'⟩) =
          p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨f, hf⟩) := by
        exact Subtype.ext (h2.trans (h4.trans (hsm u ⟨f, hf⟩).symm))
      exact congrArg Subtype.val ((p.fw.e i).injective h5)
  have key : eigLat (p.T.U ((i : ℕ) + 1)) (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ (Gk p i) =
      latTypeK p.fw p.F.lv2 i :=
    congrArg (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ⊓ ·) hAB
  rw [muCore, ← key]
end GlobalTheory.DefEig
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigSlopeLeStatement

section

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_group_actLev_char : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∃ (G : Type) (_ : Group G) (_ : Finite G) (lev : G → ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La) × ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La)) (χ : G →* (p.T.Q.c.F)ˣ), ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ slope_sq (normW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)) (eigLat (p.T.U ((i : ℕ) + 1)) lev χ (Gk p i)) ≤ muCore p i := by
  first | exact @_root_.GlobalTheory.DefEig.exists_finite_group_lev_char_slope | exact _root_.GlobalTheory.DefEig.exists_finite_group_lev_char_slope | (intros; apply _root_.GlobalTheory.DefEig.exists_finite_group_lev_char_slope <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FnAlgClosedCore

section

@[expose] public section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CoreDesc
theorem fnAlgClosed_core_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hR : _root_.GlobalTheory.CovTop.RowsTAlt p) (j : ℕ) (hj : InR D j) : FnAlgClosed (Xo := (p.T.Q.Xo j)) (c := p.T.Q.c) := by
  have hc := hR.1.ties.core
  have hpin : p.T.Q.Pins := hc.laws.pins
  have hpos : 0 < D.host.g 0 * D.host.g 1 * D.host.pde :=
    Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) D.host.pde_prime.pos
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins D p.T.Q hpin hc.canon _ hpos hc.field₁.curve j hj p.T.Q.l
    (p.T.Q.Xo j) p.T.Q.c hpin.2.1.2 ?_ rfl
  rw [hpin.2.1.1]
  exact Dvd.intro _ rfl
end GlobalTheory.CoreDesc
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsDefinedOfNotFunctionFieldAlgClosed

section

@[expose] public section



section
section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CoreDesc
theorem isDefined_of_not_functionField_algClosed_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → ¬ FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  intro _
  refine ⟨0, 0, le_rfl, ?_⟩
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A hR _ _ _ _ hF
  exact (hF (_root_.GlobalTheory.CoreDesc.fnAlgClosed_core_alt p hR _ ⟨Nat.succ_pos _, i.isLt⟩)).elim
end GlobalTheory.CoreDesc
end
section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.two_defBound_sub_unitError_le_muCore_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → ¬ FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  first | exact @_root_.GlobalTheory.CoreDesc.isDefined_of_not_functionField_algClosed_alt | exact _root_.GlobalTheory.CoreDesc.isDefined_of_not_functionField_algClosed_alt | (intros; apply _root_.GlobalTheory.CoreDesc.isDefined_of_not_functionField_algClosed_alt <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefectBoundOfConnected

section

@[expose] public section



section
section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovTop.DefCore
theorem defect_bound_of_connected_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  intro _hP
  refine ⟨0, 0, le_rfl, ?_⟩
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A hp hi hg hw hh hF
  obtain ⟨hdef, hfin, hne, hdict⟩ := _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom p i PP A 0 hp hi hg hw hh hF
  obtain ⟨G, _, _, lev, χ, hact, hfree, hsl⟩ := _root_.GlobalTheory.T.exists_finite_group_actLev_char p i PP A 0 hp hi hg hw hh hF
  have hflat := _root_.GlobalTheory.T.flatExistsAt_last_index_of_fnAlgClosed p i PP A 0 hp hi hg hw hh hF
  have h := (GlobalTheory.T.eigenlattice_slope_lower_bound_definite_case D _ _ _ _ _ _ (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) G lev χ
    (wtA (p.κ i)) (p.κ i).n _ hdef hfin hne hdict hact hfree hw.dom hg.2.2.2 hflat).2
  unfold Gk at hsl
  linarith
theorem lifts_two_mul_defBound_sub_unitE_le_muCore : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → GramAt p i → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm) - C * unitE p ≤ muCore p i := by
  intro hP
  obtain ⟨M1, C1, hC1, h1⟩ := _root_.GlobalTheory.CovTop.DefCore.defect_bound_of_connected_alt hP
  obtain ⟨M2, C2, hC2, h2⟩ := _root_.GlobalTheory.T.two_defBound_sub_unitError_le_muCore_alt hP
  have hW : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  have hH1 : _root_.GlobalTheory.CovTop.HostNAlt M1 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt M1
  have hH2 : _root_.GlobalTheory.CovTop.HostNAlt M2 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt M2
  unfold _root_.GlobalTheory.CovTop.LiftsCondition _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.HostNAlt at *
  refine Closed.imp ((hW.and hH1).and hH2) ?_
  rintro eps Fm CH - ⟨⟨⟨Cw, -, xw, hw⟩, ⟨A1, -, x1, ha1⟩⟩, ⟨A2, -, x2, ha2⟩⟩
  refine ⟨max C1 C2, le_max_of_le_left hC1, max (max xw x1) x2, fun x hx hle ι p hp i hi hg => ?_⟩
  have hle1 : xw ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hle2 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have hle3 : x2 ≤ x := le_trans (le_max_right _ _) hle
  have w := hw x hx hle1 ι p hp i
  have a1 := ha1 x hx hle2 ι p hp i
  have a2 := ha2 x hx hle3 ι p hp i
  have hu := unitE_nonneg p i _ _ _ w a1
  by_cases hF : FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c)
  · have := h1 p i _ _ hp hi hg w a1 hF
    nlinarith [le_max_left C1 C2]
  · have := h2 p i _ _ hp hi hg w a2 hF
    nlinarith [le_max_right C1 C2]
end GlobalTheory.CovTop.DefCore
end
end
section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.two_mul_defBound_sub_le_muCore_of_gramAt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → GramAt p i → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm) - C * unitE p ≤ muCore p i := by
  first | exact @_root_.GlobalTheory.CovTop.DefCore.lifts_two_mul_defBound_sub_unitE_le_muCore | exact _root_.GlobalTheory.CovTop.DefCore.lifts_two_mul_defBound_sub_unitE_le_muCore | (intros; apply _root_.GlobalTheory.CovTop.DefCore.lifts_two_mul_defBound_sub_unitE_le_muCore <;> assumption)
end
end
end
end

module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAdmAt
public import Formalism.LocalToGlobal.InertKernelTheory.TranslatesOfInertKernelAtPlace
public import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelCoupledLastLift
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
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
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.OrbitSumStabilizer
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Formalism.LocalToGlobal.InertKernelTheory.AdmissibleEleventhInert
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelSmallOfFrameTwist
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelCoupled
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelInstances
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.LatticeShapeMiddleHolds
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PositivityConditionHolds

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.ThetaSeriesDataHypothesesBelowMaximalLevel

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.AdmLoc2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)

def StabLawLt (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L0 : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (ε : (X.Lv.lev j c).Γ),
    (c, L0) ∈ repOf X.Lv hfin j → (X.Pj (j + 1)).IsLatTup La'.2 → (X.Lv.lev j c).smul ε L0 = L0 →
      MvPowerSeries.C ((kapG X ℂ_[p] j c ε)⁻¹) * SA X ℂ_[p] j (gamAt X j c ε) (ThR j (c, L0) La') = ThR j (c, L0) La'

end Law

section Gen

variable {p : ℕ} [Fact p.Prime] {D : D7}

def ThetaSeriesDataHypothesesBelowMaximalLevel (X : Sys p) (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  Formalism.L2.KerInert.RepLt.AdmGLt X hfin D fd ∧ Formalism.L2.KerInert.RepRec.ClAway p cl ∧ Formalism.L2.KerInert.KGLt.XiAwayLt X hfin D Ξ₀ ∧
    Formalism.L2.KerInert.RepLt.ScalGLt X hfin fd χ muT lam ∧
    ∃ ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v,
      Formalism.L2.KerInert.RepFrame.LamPosG X E D pos lam ρ ∧ Formalism.L2.KerInert.RepFrame.MInv X fd.frM ∧
      Formalism.L2.KerInert.RepLt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ

def LawInLt (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (E : CEmbC X.G)
    {g : GL3Theta.G1 p} (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (fd : FData X D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  StabLawLt X E.toCEmb hfin (thFOf X pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT)))

end Gen

def AdmGen2 : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ),
    CurveIn D p cc δ g B χ lam → ThetaSeriesDataHypothesesBelowMaximalLevel X E hfin pos fd χ lam cl Ξ₀ muT →
    XiIn X E hfin hst hLT pos fd B χ lam SS cl Ξ₀ muT → LawInLt X hfin E hLT pos fd B χ lam SS cl Ξ₀ muT →
    adm3b D X → ArchimedeanSignatureMatching D X (pendG X E hfin hst hLT pos fd B χ lam SS cl Ξ₀ muT) →
      admitted D X (pendG X E hfin hst hLT pos fd B χ lam SS cl Ξ₀ muT)


open Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelCoupled in
def AdmAt2 : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    [IsFractionRing (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.O (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.Kf] (E : CEmbC (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G)
    (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (hst : FinStab (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv)
    (g : GL3Theta.G1 (D.what₂.places.resChar w)) (hLT : LTIso g)
    (pos : (Σ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl, Fin ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.n' v)) ≃ D.what₂.Tau)
    (Tw : TwForms D) (I : Formalism.MainNotions.G.CmpJ.CmpJIn Tw u μ w h Lv) (L0 : Formalism.L2.PairingIndexBounds.F.Lev0Data D u w h)
    (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
      Formalism.L2.Col.HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ),
    CurveIn D (D.what₂.places.resChar w) cc δ g B χ lam →
    ThetaSeriesDataHypothesesBelowMaximalLevel (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ lam cl Ξ₀ muT →
    XiIn (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    LawInLt (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin E hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    (∃ ι Rd Sr, (∀ j, j + 1 < D.R.m → TiesAt (Y := (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT)) t u μ KA.cls KA.cmp ι Rd Sr j) ∧
      (0 < D.R.m → ∃ lp, TiesC (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT) t u μ KA.cmp ι Rd Sr (D.R.m - 1) lp ∧ HeckeC (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT) u μ (D.R.m - 1) lp)) →
      admitted D (sysAt Ch std vp unif eO eO_spec dG dG_spec om) (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT)


open Formalism.L2.KerInert.SecondKernelInstances in
def AdmAtEnt2 : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    [IsFractionRing (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.O (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.Kf] (E : CEmbC (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G)
    (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (hst : FinStab (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv)
    (g : GL3Theta.G1 (D.what₂.places.resChar w)) (hLT : LTIso g)
    (pos : (Σ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl, Fin ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.n' v)) ≃ D.what₂.Tau)
    (Tw : TwForms D) (I : Formalism.MainNotions.G.CmpJ.CmpJIn Tw u μ w h Lv) (L0 : Formalism.L2.PairingIndexBounds.F.Lev0Data D u w h)
    (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
      Formalism.L2.Col.HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ),
    CurveIn D (D.what₂.places.resChar w) cc δ g B χ lam →
    ThetaSeriesDataHypothesesBelowMaximalLevel (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ lam cl Ξ₀ muT →
    XiIn (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    LawInLt (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin E hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    (∃ ι Rd Sr, ∀ j < D.R.m,
      TiesAt (Y := pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT) t u μ KA.cls KA.cmp ι Rd Sr j) →
      admitted D (sysAt Ch std vp unif eO eO_spec dG dG_spec om) (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT)

end Formalism.L2.KerInert.AdmLoc2
end
end
end

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.AdmissibleAllLevels

section

@[expose] public section

namespace Formalism.L2.KerInert

def Adm8All : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p), Formalism.MainNotions.FormalGroupSystem.adm8 D X

theorem admissible_all_levels : Adm8All := fun D _ _ X =>
  ⟨Formalism.MainNotions.G.LatticeSystems.exponent_condition_holds D X.G, (Formalism.L2.G.Model.operators_preserve_lattices D X.G).2⟩

end Formalism.L2.KerInert
end
end

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw

section

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert.AdmLoc2

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (be : MvPowerSeries (Fin 2) (Formalism.L2.G.Pend.K0 p))

theorem admissible_stabilizer_of_law (D : Formalism.BasicNotions.D7) (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) :
    StabLawLt X E hfin ThR → Formalism.MainNotions.FormalGroupSystem.MinkowskiCounting D X (pendR X E hfin hst be ThR) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  intro hS
  classical
  let ThR' : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p] :=
    fun j La La' => if j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2 then ThR j La La' else 0
  have hS' : StabLaw X ℂ_[p] hfin ThR' := by
    intro j c L0 La' ε h0 hε
    by_cases hj : j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2
    · simp only [ThR', if_pos hj]
      exact hS j hj.1 c L0 La' ε h0 hj.2 hε
    · simp only [ThR', if_neg hj]
      unfold SA
      rw [← MvPowerSeries.coe_substAlgHom (hasSubst_actS X ℂ_[p] j _), map_zero, mul_zero]
  have hK := kapLaw_of_stabLaw X ℂ_[p] hfin ThR' pC_ne_zero hS'
  intro j hj c L La' γ G hGv hL hLa'
  have hEq : ∀ La, thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR') j La La' = thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j La La' := by
    intro La
    simp only [thFN, thGeo, ThR', if_pos (And.intro hj hLa')]
  have key : ∀ t : X.G.Kf,
      (eSX X j (c, (X.Lv.lev j c).smul γ L) * t) •
          delF X ℂ_[p] j ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G)
            (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, (X.Lv.lev j c).smul γ L) La') =
        (eSX X j (c, L) * t) • delF X ℂ_[p] j G (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, L) La') := by
    intro t
    have := ker_law X ℂ_[p] pC_ne_zero (delEquivOn_GdC X ℂ_[p]) _ hK j c L La' γ G hL (vtIn_GdC X ℂ_[p] j G hGv) t
    rwa [hEq, hEq] at this
  exact key _

end Law

end Formalism.L2.KerInert.AdmLoc2

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.AdmLoc2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)

theorem admissible_general_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmGen2 := by
  intro D p _ X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw h3b h4
  obtain ⟨h5, hAt, hin, hW, hcc, hδ, hχ, hlam, hLam⟩ := hC
  obtain ⟨hA, hcl, hXa, hS, ρ, hLP, hMI, hFL⟩ := hK
  obtain ⟨h2, h2b, h3⟩ := hK1 D p h5 X E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ
    hAt hin hW hcc hδ hχ hlam hLam hA hcl hXa hS hLP hMI hFL
  refine ⟨Formalism.MainNotions.FormalGroupSystem.Pf.positivity_condition_holds D, h2, h2b, ?_, h3, h3b, h4, ?_, ?_, Formalism.L2.G.Pend.up_down_adjoint D X _,
    Formalism.L2.PairingIndexBounds.Ent.pending_tuple_admissible X E hfin hst hLT pos _ D, Formalism.L2.KerInert.admissible_all_levels D p X, ?_⟩
  · exact Formalism.L2.KerInert.admissible_second_inert D cc δ p g hLT hAt h5 hin hW X _ rfl
  · exact (invariance_iff_additive_maps_exist X E hfin hst hLT pos _ D).2 hXi
  · exact admissible_stabilizer_of_law X E.toCEmb hfin hst (beLT hLT) D _ hLaw
  · exact Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hin hW X _ rfl

section At

open Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelCoupled

theorem admissible_place_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hE, hL⟩ := hTies
  have hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m := KA.fl_m
  refine admissible_general_of_kernel_law hK1 D _ (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst g hLT pos _ cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw
    (admissible_third_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om) ?_
  by_cases hm : 0 < D.R.m
  · obtain ⟨lp, hTC, hH⟩ := hL hm
    exact admissible_fourth_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hE (fun _ => ⟨hTC, hH⟩)
  · exact ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩

theorem admissible_entries_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAtEnt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hA⟩ := hTies
  have h5b := admissible_stabilizer_of_law (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E.toCEmb hfin hst (beLT hLT) D _ hLaw
  refine admissible_place_of_kernel_law hK1 D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om E hfin hst g hLT pos Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT
    hC hK hXi hLaw ⟨ι, Rd, Sr, fun j hj => hA j (by omega), fun hm => ?_⟩
  obtain ⟨lp, hsec⟩ := coupled_section_exists D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ hm
  have hT1 := hA (D.R.m - 1) (by omega)
  exact ⟨lp, coupled_compatibility_at_place D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hm hsec hT1,
    hecke_coupled_entry D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ lp hm h5b hsec hT1.2.1⟩

end At

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem admissible_entries_small_chain : AdmAtEnt2 := admissible_entries_of_kernel_law Formalism.L2.KerInert.KGLt.first_kernel_law_global_small

end Formalism.L2.KerInert.AdmLoc2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertThetaAdmissibilityOfComplexMultiplication

section

@[expose] public section

namespace GlobalTheory.TwV.Lt

theorem inert_theta_admissibility_of_complex_multiplication : Formalism.L2.Th1.CM.CM2 → GlobalTheory.TwV.Lt.AdmAtEnt2 := fun h => by
  haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
  exact Formalism.L2.KerInert.AdmLoc2.admissible_entries_small_chain

end GlobalTheory.TwV.Lt
end
end

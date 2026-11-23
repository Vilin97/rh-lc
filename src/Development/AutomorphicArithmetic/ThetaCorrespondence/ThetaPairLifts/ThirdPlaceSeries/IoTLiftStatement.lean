module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXTLevelPStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalar

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.IoTop

theorem liftS_smul_domain {D : D7} {S T : HSp D} (om : Om S T) (ν μ : Measure (GA D T)) (c : ENNReal) (hc0 : c ≠ 0)
    (hμ : μ = c • ν) (hH : μ.IsHaarMeasure) {𝓕 𝓖 : Set (GA D T)} (h₁ : IsFundamentalDomain (GQ T) 𝓕 μ)
    (h₂ : IsFundamentalDomain (GQ T) 𝓖 ν) (G : GA D T → ℂ) (φ : WO S T → ℂ) (x : GA D S)
    (hinv : ∀ γ ∈ GQ T, ∀ y, om (x, γ * y) φ 0 * G (γ * y) = om (x, y) φ 0 * G y) :
    liftS om μ 𝓕 G φ x = (c.toReal : ℂ) • liftS om ν 𝓖 G φ x := by
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : Countable (GQ T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig T.gram
  have h₂' : IsFundamentalDomain (GQ T) 𝓖 μ := h₂.mono (hμ ▸ Measure.smul_absolutelyContinuous)
  rw [liftS_apply, liftS_apply, h₁.setIntegral_eq h₂' fun γ y => hinv γ.1 γ.2 y, hμ, Measure.restrict_smul,
    integral_smul_measure, Complex.real_smul]
  rfl

theorem smul_const (a b : ℝ) (H z : ℂ) (hab : 0 ≤ a * b) :
    ((ENNReal.ofReal (a * b)).toReal : ℂ) • (H • z) = (H * (a : ℂ) * (b : ℂ)) • z := by
  rw [ENNReal.toReal_ofReal hab, smul_eq_mul, smul_eq_mul, smul_eq_mul, Complex.ofReal_mul]
  ring

end GlobalTheory.Fam.IoTop


end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoTLift

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.IoTop
theorem omT_weil_chr {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    (hc : W.Q.Rl.Char3 W.Q.F) (t : W.P.T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2 (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X' (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX t) e) := by
    rintro n rfl
    exact hc.chain.ωX t
  exact key (j + 1) (idx_top h)
end GlobalTheory.Fam.IoTop

open GlobalTheory.Fam.IoTop in
theorem GlobalTheory.Fam.liftS_ptT_eq_cI_smul_ioT : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → ∀ t j (h : j + 2 * 0 + 2 = D.R.m) (F : (f.t t).CT) P v, liftS ((f.t t).omT j h) f.c.volT.μ f.c.volT.𝓕 (F.1 v) ((f.t t).ptT j h P) = (f.t t).cI (j + 1) • ((f.t t).ioT j h F).1 (f.c.ItT j h P v) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR t j h F P v
  have hc := hP.bot.hyp.2.2.2.1
  obtain ⟨h', -, hL⟩ := _root_.GlobalTheory.T.extra_column_range_membership_alt W u hP f.g t j h F
  have key := hL ((f.row t).vT j h) ((hR.row t).vT j h) P v
  obtain ⟨h'', hio⟩ := (hR.row t).ioT j h F
  have hm := hR.meas.volT t
  rw [show D.R.m - 1 = j + 1 by omega, show f.g.κ D.R.m = f.g.κ (j + 1 + 1) from congrArg f.g.κ (by omega)] at hm
  have hom := _root_.GlobalTheory.Fam.IoTop.omT_weil_chr W hc t j h
  have hth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X'
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) ((f.row t).vT j h) P) := by
    obtain ⟨cY, hcY⟩ := hc.lev.βY (j + 1) (by omega)
    obtain ⟨cX', hcX⟩ := hc.lev.βX
    have hf := (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcY) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcX) hcY.1 hcX.1
      ((hR.row t).vT j h)
    have e0 : ∀ (V : HSp D) (ρ : D.what₂.Tau), compAt (_root_.GlobalTheory.Fam.pk_z W).θ ρ (Formalism.L2.Theta.mt V 1) = 1 := fun V ρ => by
      have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this]
      exact Matrix.map_one _ (by simp) (by simp)
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hom hc.models.inf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
      (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) 1 1
      (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) _ hf P).1
  have hκ := hR.meas.κ (j + 1 + 1)
  have hvl : 0 ≤ volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t (j + 1) := by unfold volLev; split_ifs <;> exact ENNReal.toReal_nonneg
  have hc0 : ENNReal.ofReal (f.g.κ (j + 1 + 1) * volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t (j + 1)) ≠ 0 := by
    have := (hR.meas.cIOf_ne_zero (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1) (by omega))
    unfold cIOf at this
    intro h0
    rw [ENNReal.ofReal_eq_zero] at h0
    refine this ?_
    have : f.g.κ (j + 1 + 1) * volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t (j + 1) = 0 := le_antisymm h0 (mul_nonneg hκ.le hvl)
    rw [mul_assoc, ← Complex.ofReal_mul, this, Complex.ofReal_zero, mul_zero]
  have hfd := (hc.models.νX t).2
  show liftS (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) f.g.volT.μ f.g.volT.𝓕 (F.1 v) _ = cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g t (j + 1) • _
  funext x
  have e1 := liftS_smul_domain (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) ((_root_.GlobalTheory.Fam.pk_z W).νX t) f.g.volT.μ _ hc0 hm f.g.volT.haar f.g.volT.fund hfd
    (F.1 v) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
      (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) ((f.row t).vT j h) P) x (fun γ hγ y => by
        have a1 : (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) (x, γ * y) = (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) (1, γ) * (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) (x, y) := by
          rw [← map_mul, Prod.mk_mul_mk, one_mul]
        rw [a1, Module.End.mul_apply, hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres _ _ hth),
          GlobalTheory.ChainLiftEquiv.multT_left _ _ _ _ F.1 F.2 v γ hγ y])
  have hio' : (((f.t t).ioT j h) F).1 = ((ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h) ⟨F.1, h'⟩).1 := hio
  have e2 : (((f.t t).ioT j h) F).1 (((f.c.ItT j h) P) v) x = ((ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h) ⟨F.1, h'⟩).1 (((f.c.ItT j h) P) v) x :=
    congrFun (LinearMap.congr_fun hio' _) x
  have e3 := congrFun key x
  rw [Pi.smul_apply] at e3
  exact e1.trans ((congrArg _ e3).trans ((smul_const _ _ _ _ (mul_nonneg hκ.le hvl)).trans (congrArg _ e2.symm)))
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoTLiftStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lift_s_last_eq_ci_succ_smul_io : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → ∀ t j (h : j + 2 * 0 + 2 = D.R.m) (F : (f.t t).CT) P v, liftS ((f.t t).omT j h) f.c.volT.μ f.c.volT.𝓕 (F.1 v) ((f.t t).ptT j h P) = (f.t t).cI (j + 1) • ((f.t t).ioT j h F).1 (f.c.ItT j h P v) := by
  first | exact @_root_.GlobalTheory.Fam.liftS_ptT_eq_cI_smul_ioT | exact _root_.GlobalTheory.Fam.liftS_ptT_eq_cI_smul_ioT | (intros; apply _root_.GlobalTheory.Fam.liftS_ptT_eq_cI_smul_ioT <;> assumption)
end
end
end

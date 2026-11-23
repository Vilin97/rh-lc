module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameFOfDiv
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsoPairToTermSymm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarVolPf
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhLocOfIntegrablePh
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfLowest
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RegUnitary
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdIndexEq
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhConvProj
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhProdConv
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhSchurConv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionD
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CdScaleEqCdScaleOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepPuVolAR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RefilledStagesRecord
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermData
public import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolFormalDegreeEq

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem covol_formalDegree_eq : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D →
    Formalism.MainNotions.StandardLattice.VolTie D → cdScaleTie D → dsigTie D →
    (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal =
      Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ :=
  fun _D X h hVol hcd hT => Formalism.L2.SG.Pf.DstarVolPf.dstarVol_holds X h hVol hcd hT

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DEqFinrankHHX

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.RowsCount


open Formalism Formalism.L2 Formalism.L2.SG in
theorem projRowsR : Formalism.L2.SG.ProjRows.ProjRowsR :=
  Formalism.L2.SG.ProjRows.projRowsR_of schur_orthogonality_idempotent convolution_projection isConvIdempotent_pi
    Formalism.L2.SG.Pf.regular_representation_unitary


open Formalism Formalism.L2 Formalism.L2.SG in
theorem unimodGf : Formalism.L2.SG.Pf.UnimodGf := fun I μf _ _ =>
  (PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable
    PI.adelic_index_eq) I μf inferInstance

theorem D_eq_finrank_HHX : ∀ (D : D7) (X : HidaSetting D),
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → X.B.D = Module.finrank ℂ (HHX X) := by
  intro D X h
  exact (Formalism.L2.SG.RowsDef.RowsAut.D_eq_finrank_HH (Formalism.L2.SG.Pf.rows_bijective projRowsR unimodGf) X.B _
    (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X) (fun v => (X.low v).1)
    (GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X h) X.Rph X.Rph_spec).1

end GlobalTheory.RowsCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FEqAndRdEq

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace GlobalTheory.DegreeRankEquations

theorem f_eq (D : D7) (X : HidaSetting D) : X.B.I.f = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  unfold AutInst.f
  omega

theorem rd_eq (D : D7) (X : HidaSetting D) : X.B.I.rd = D.host.rdE := by
  have hd : discr X.B.I.E = discr D.host.E := NumberField.discr_eq_discr_of_algEquiv X.B.I.E X.ιE.toRatAlgEquiv
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : (Module.finrank ℚ D.host.E : ℝ) = 2 * (X.B.I.f : ℝ) := by
    unfold AutInst.f
    have : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ X.B.I.F := by rw [← e1, ← e2, e3, mul_comm]
    rw [this]; push_cast; ring
  unfold AutInst.rd Host.rdE
  rw [hd, e4]

end GlobalTheory.DegreeRankEquations
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.Chi2ApplyOne

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.BundleTie

variable {D : D7} (X : HidaSetting D)

theorem chi2_apply_one : X.chi2 1 = 1 := by

  obtain ⟨h1, -, -, hmul, hnorm⟩ := Formalism.L2.SG.Pf.level_subgroup_character_unitary X
  have hsq := hmul 1 h1 1 h1
  rw [mul_one (1 : X.B.I.Gf)] at hsq
  have hne : X.chi2 1 ≠ 0 := by
    intro h0
    have hn := hnorm 1 h1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact hsq.symm)

theorem e_one : X.B.e 1 = 1 / (X.volK2 : ℂ) := by
  have h1 : (1 : X.B.I.Gf) ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := (Formalism.L2.SG.Pf.level_subgroup_character_unitary X).1
  rw [X.e_eq 1, if_pos h1]
  have hc : chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd 1 = 1 := chi2_apply_one X
  rw [hc, star_one]
  rfl


open Formalism Formalism.L2 Formalism.L2.SG in
theorem dstarD_eq
    (hI : (X.B.μf X.B.I.Kset).toReal / X.volK2 = Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1))
    (hV : (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal =
      Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ) :
    Formalism.MainNotions.StandardLattice.DstarD D =
      X.B.I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.μf X.B.fund X.B.e := by
  have hre : (X.B.e 1).re = 1 / X.volK2 := by
    rw [e_one X, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hd : (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) = ∏ v, X.dv v := rfl
  have hsub : X.K2 ⊆ X.B.I.Kset := fun x hx => hx.1
  have hv2 : X.volK2 = (X.B.μf X.K2).toReal := rfl
  show Formalism.MainNotions.StandardLattice.volY0 D * Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ ρ, D.dsig ρ =
    (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) * X.B.I.vol X.B.μf X.B.fund * (X.B.e 1).re
  rw [hre, hd, ← hI]
  by_cases hv : X.volK2 = 0
  · rw [hv]
    simp
  ·
    have hK2 : X.B.μf X.K2 ≠ 0 := by
      intro h
      apply hv
      simp [hv2, h]
    have hμ : (X.B.μf X.B.I.Kset).toReal ≠ 0 := by
      rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨fun h => hK2 (measure_mono_null hsub h),
        (PI.WAU.Cpt.isCompact_Kset X.B.I).measure_lt_top.ne⟩
    calc Formalism.MainNotions.StandardLattice.volY0 D * ((X.B.μf X.B.I.Kset).toReal / X.volK2) * ∏ ρ, D.dsig ρ
        = (Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ) * (X.B.μf X.B.I.Kset).toReal / X.volK2 := by ring
      _ = ((∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal) *
            (X.B.μf X.B.I.Kset).toReal / X.volK2 := by rw [hV]
      _ = (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund * (1 / X.volK2) := by
        rw [div_mul_cancel₀ _ hμ, mul_one_div]

theorem autTie : ∀ (D : D7) (X : HidaSetting D), Nonempty (D.s.HH ≃ₗᵢ[ℂ] HHX X) →
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → D.what₂.Dstar = Formalism.MainNotions.StandardLattice.DstarD D →
    X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Formalism.MainNotions.StandardLattice.VolTie D → cdScaleTie D → dsigTie D →
    AutTie D X.B X.pl := by
  intro D X hHH hint hD hinst hVol hcd hds
  obtain ⟨ι⟩ := hHH
  have hV := GlobalTheory.covol_formalDegree_eq D X hinst hVol hcd hds
  have hI := Formalism.L2.SG.Pf.DstarIdxPf.dstarIdx_holds X
  exact
    { n_eq := X.n_eq
      f_eq := GlobalTheory.DegreeRankEquations.f_eq D X
      rd_eq := GlobalTheory.DegreeRankEquations.rd_eq D X
      eps_eq := X.eps_eq
      lam_eq := X.lam_eq
      ds := X.ds
      low := X.low
      g_eq := X.g_eq
      g0_eq := X.g0_eq
      D_eq := by
        rw [GlobalTheory.RowsCount.D_eq_finrank_HHX D X hint, ← ι.toLinearEquiv.finrank_eq, D.s_HH]
      Dstar_eq := hD.trans (dstarD_eq X hI hV) }

end GlobalTheory.BundleTie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealReS

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem real_reS : ∀ (D : D7) (Z : SNew D), (Formalism.L2.Theta.RealTied D → Formalism.L2.Theta.RealTied (reS D Z)) ∧ StandardLattice.DstarD (reS D Z) = StandardLattice.DstarD D ∧ (StandardLattice.VolumeEqMass₂ D → StandardLattice.VolumeEqMass₂ (reS D Z)) :=
  fun _ _ => ⟨fun h => ⟨h.cdScale, h.dsig, h.dsig_all, h.vol⟩, rfl, fun h => h⟩

end GlobalTheory.Mem.SRe
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSRestRe

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

section Core

variable {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall)
  (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)
  (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y))



def sIsoRe (hR : Formalism.L2.Theta.RealTied D) (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) :
    SIso (reD D ⟨P.toNew hD j, N, hh⟩).s (sOf hF) where
  cd := by
    have h := (real_reS D (P.toNew hD j)).1 hR
    exact cdScale_eq_cdScaleOf (reD D ⟨P.toNew hD j, N, hh⟩) ((by with_unfolding_all exact (h.cdScale :)))
  del := rfl
  letter := rfl
  eHH := (by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))
  eCu := fun u => (by with_unfolding_all exact (eCure ⟨P.toNew hD j, N, hh⟩ P.fin hF u :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).1 :))
  volN := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).1 :))
  volH := by
    funext u
    exact (by with_unfolding_all exact (((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.1 u).2 :))
  eT := fun u u' => (by with_unfolding_all exact (eRT ⟨P.toNew hD j, N, hh⟩ P.Y u u' :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF).2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => by
    apply Subtype.ext
    exact (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.1 :))
  atP := fun p => (by with_unfolding_all exact ((hL p).some :))
  ePl := (by with_unfolding_all exact (Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.1 q :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.1 :))
  eP := fun u u' => (by with_unfolding_all exact ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose :))
  pfst := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1 :))
  psnd := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.1 :))
  s0 := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.1 :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.1 :))
  pval := fun {u u'} p => (by with_unfolding_all exact (((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).2.2.2.2 :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} (p : RP P.Y u u') => by
    have h1 := ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').1 p.1.1).2.2.2.2.2.2.2.2.1
    have h2 := ((rp_iso_pair D ⟨P.toNew hD j, N, hh⟩ P.X P.Y P.fin hF u u').choose_spec p).1
    exact (by with_unfolding_all exact (h1.trans (congrArg (fun t => Formalism.L2.SG.PairVal.massTerm t) h2) :))
  meanCount := by
    funext u u' w
    exact (by with_unfolding_all exact ((eRT_keeps_term_data D ⟨P.toNew hD j, N, hh⟩ P.X P.Y u u').2 w :))

end Core

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe



theorem exists_sRest_re : ∀ (D : D7) (F : ∀ u, Forms0 D u) (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F F') (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)), Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.Theta.RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → ∃ S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  intro D F P hD j N hh F' hs hF hph hL hR hDs
  have hR' := (real_reS D (P.toNew hD j)).1 hR
  have hDs' : (reD D ⟨P.toNew hD j, N, hh⟩).what₂.Dstar = StandardLattice.DstarD (reD D ⟨P.toNew hD j, N, hh⟩) := (by with_unfolding_all exact (hDs.trans (real_reS D (P.toNew hD j)).2.1.symm :))
  have hAut : Formalism.MainNotions.S.AutTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.B
      (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X.pl :=
    GlobalTheory.BundleTie.autTie (reD D ⟨P.toNew hD j, N, hh⟩) (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).X
      ⟨(by with_unfolding_all exact (eHHre ⟨P.toNew hD j, N, hh⟩ P.X :))⟩ ((by with_unfolding_all exact (hph :))) hDs' (P.re ⟨P.toNew hD j, N, hh⟩ hs hF).inst
      ((by with_unfolding_all exact (Formalism.L2.Theta.VolTieG.volTie hR'.vol :))) ((by with_unfolding_all exact (hR'.cdScale :))) ((by with_unfolding_all exact (hR'.dsig_all :)))
  refine ⟨⟨sIsoRe P hD j N hh hF hR hL, hAut, ?_, j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G), ?_, (by with_unfolding_all exact (hL :))⟩, rfl⟩
  · intro u x
    apply Subtype.ext
    exact (by with_unfolding_all exact (colDictL_reTr ⟨P.toNew hD j, N, hh⟩ (P.tr u) (hs u).2.1 (hs u).2.2 P.Y.hK x :))
  · intro x
    exact (by with_unfolding_all exact ((conjHH_eEECre ⟨P.toNew hD j, N, hh⟩ P.G (j x)).symm :))

end GlobalTheory.Mem.SRe
end
end
end

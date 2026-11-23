module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiAlgUnitInert
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
public import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePointDetNormOneOrderEqNegLengthStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLambdaCharacterNormOneIdeleEqPPowStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SystemWeightsEqShiftedCharacterExponentsStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealNormOneAndCharUnitarySmul

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.DetIdealUnitary

theorem determinantIdeal_normOne_and_char_unitary_smul : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∧ ∀ e : Matrix (Fin N) (Fin N) D.host.E, e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e L)) = (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  letI := fun D : D7 => D.host.cmStar
  intro D χ hχ N L hN hsd
  refine ⟨Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hsd, ?_⟩
  intro e he
  have hu : e ∈ Matrix.unitaryGroup (Fin N) D.host.E := Matrix.mem_unitaryGroup_iff.2 he
  have h := GlobalTheory.Mem.NatEqui.chi_smulLat hχ (L := L) hsd ⟨e, hu⟩
  rw [Finset.prod_inv_distrib] at h
  exact h

end GlobalTheory.DetIdealUnitary
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealNormOneAndCharUnitarySmulStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem _root_.GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∧ ∀ e : Matrix (Fin N) (Fin N) D.host.E, e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e L)) = (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  first | exact @GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul | exact GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul | (intros; apply GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul <;> assumption)
end
end

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MInvFdOfCharts

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.ScalM

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

section lamC

variable {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

theorem qbar_zpow_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (n : ℤ) : s ^ n ∈ TaylorLogMetric.Qbar := by
  cases n with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hs k
  | negSucc k =>
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hs _)

theorem lamC_of_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam s = lam ⟨s, hs⟩ := by
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hs]

theorem lamC_mul_mem {s t : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (ht : t ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (s * t) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam t := by
  rw [lamC_of_mem lam (TaylorLogMetric.Qbar.mul_mem hs ht), lamC_of_mem lam hs, lamC_of_mem lam ht, ← map_mul]
  rfl

theorem lamC_inv_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam s⁻¹ = (TaylorLogMetric.lamC lam s)⁻¹ := by
  rw [lamC_of_mem lam (TaylorLogMetric.Qbar.inv_mem hs), lamC_of_mem lam hs, ← map_inv₀]
  rfl

theorem lamC_zpow_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (n : ℤ) : TaylorLogMetric.lamC lam (s ^ n) = (TaylorLogMetric.lamC lam s) ^ n := by
  rw [lamC_of_mem lam (qbar_zpow_mem hs n), lamC_of_mem lam hs, ← map_zpow₀]
  rfl

end lamC

section minv

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}

end minv

section scal

variable {p : ℕ} [Fact p.Prime] {D : D7} (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (fd : FData X D)
  (χ : TaylorLogMetric.IdE D → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
  (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

variable {X hfin fd χ muT lam}

end scal

end Formalism.L2.KerInert.ScalM

namespace Formalism.L2.KerInert.ScalM

open Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section inst

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)

end inst

end Formalism.L2.KerInert.ScalM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesScalarBoundedOfPosPair

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.KerInert.ScalM (qbar_zpow_mem lamC_mul_mem lamC_inv_mem lamC_zpow_mem)

noncomputable section

namespace GlobalTheory.TwV.Xc



theorem scal_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, -, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  obtain ⟨hp5, -, hIn, -, -, -, hχ, -, -⟩ := S.curve
  have hp2 : D.what₂.places.resChar w ≠ 2 := by omega
  intro j hj L0 hL0 La' hLa'
  have hj' : j < D.R.m := hmm ▸ hj
  have hL0lat : ((sysS H X std).Pj j).IsLatTup L0.2 := Formalism.L2.G.Pend.repOf_lat _ S.hfin j L0 hL0
  obtain ⟨hAdm, -, -, -, -, -, -, -⟩ := hPair j hj L0 La' hL0lat hLa'
  obtain ⟨hN, hN', hsd, hsd'⟩ := hAdm
  obtain ⟨ha, -, hu⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN hsd).1
  obtain ⟨ha', -, hu'⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN' hsd').1
  obtain ⟨hU0, hord0⟩ := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS j hj'.le L0 hL0lat
  obtain ⟨hU1, hord1⟩ := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS (j + 1) hj' La' hLa'
  have hfill := GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj' La'.1
  have hm1 := S.law.mu_alg j hj' _ hU1
  have hm0 := S.law.mu_alg j hj' _ hU0
  have hn1 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU1
  have hn0 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU0

  have hcf : Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    unfold Base.chiFac
    exact TaylorLogMetric.Qbar.mul_mem (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _)
  have hcfn : ‖TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La'))‖ = 1 := by
    unfold Base.chiFac
    rw [lamC_mul_mem S.lam (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _), lamC_zpow_mem S.lam ha,
      lamC_zpow_mem S.lam ha', norm_mul, norm_zpow, norm_zpow, hu, hu', one_zpow, one_zpow, mul_one]
  have hmr : S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hm1 (TaylorLogMetric.Qbar.inv_mem hm0)
  refine ⟨?_, ?_⟩
  · unfold KG.scalG
    exact TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
      (qbar_zpow_mem ha' _)
  have hexp : TaylorLogMetric.lamC S.lam (KG.scalG (J.fd std) t.χ S.muT j L0 La') =
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
        (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)) := by
    unfold KG.scalG
    rw [lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
        (qbar_zpow_mem ha' _),
      lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _),
      lamC_mul_mem S.lam hmr (TaylorLogMetric.Qbar.inv_mem hcf), lamC_inv_mem S.lam hcf, lamC_zpow_mem S.lam ha, lamC_zpow_mem S.lam ha']
  have hp0 : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact_mod_cast (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hB' : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ = 1 := by
    rw [lamC_mul_mem S.lam hm1 (TaylorLogMetric.Qbar.inv_mem hm0), lamC_inv_mem S.lam hm0, norm_mul, norm_mul, norm_inv, norm_zpow,
      hn1, hn0, ← zpow_neg, ← mul_assoc, ← zpow_add₀ hp0, ← zpow_add₀ hp0]
    convert zpow_zero (‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖) using 2
    simp only [hord1, hord0, KG.expG, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun v _ => by ring
  rw [hexp]
  calc ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
        (TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
          (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))‖
      = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
          TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, norm_mul, norm_mul, norm_mul, norm_inv, norm_zpow, norm_zpow, hcfn, hu, hu',
          one_zpow, one_zpow, inv_one, mul_one, mul_one, mul_one]
    _ = 1 := hB'
    _ ≤ 1 := le_rfl

end GlobalTheory.TwV.Xc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesScalarBoundedOfPosPairStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → S.Scal) := by
  first | exact @GlobalTheory.TwV.Xc.scal_of_pos_pair | exact GlobalTheory.TwV.Xc.scal_of_pos_pair | (intros; apply GlobalTheory.TwV.Xc.scal_of_pos_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesScalarPowIntegral

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem scal_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hd
  exact GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair S hd ⟨J.alg0, J.alg⟩ (pos_at_site S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hd)

end GlobalTheory.TwV
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesScalarPowIntegralStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelSite_seriesScalar_pow_integral : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  first | exact @GlobalTheory.TwV.scal_at_site | exact GlobalTheory.TwV.scal_at_site | (intros; apply GlobalTheory.TwV.scal_at_site <;> assumption)
end
end

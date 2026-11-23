module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsSphSec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantSphericalCoefficientEqZeroOrZonalStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumUnramifiedZetaSumUnitaryInert
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalDoublingSectionGraphDiagonalEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNormCosetOutStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransportStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumDoublingInert

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.DoublingSumU



theorem hasSum_doubling_inert : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ χ : Lˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ m : ℕ, ((χ ϖ : ℂˣ) : ℂ) = (-1) ^ m → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q (χ ϖ) s) α) → (∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g)) ∧ HasSum (fun a : GU σ n ⧸ KU σ n => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n a.out) * ℓ (ρ a.out x)) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL q n α (χ ϖ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac q n m s * ℓ x) := by
  intro hD L _ _ _ ϖ σ q n hU χ hχ m hm s Φ hΦ V _ _ ρ x α hx ℓ hℓ hdom
  have hright : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) := by
    intro g k hk
    obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := GlobalTheory.ZetaSumU.cartan_complete L (ϖ : L) σ q n hU g
    rw [mul_assoc (a * t) b k, GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha _ (mul_mem hb hk),
      GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha b hb]
  refine ⟨hright, ?_⟩
  obtain ⟨h0, h1⟩ := GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal L ϖ σ q n hU V ρ x α hx ℓ hℓ
  by_cases hx0 : ℓ x = 0
  · simp only [h0 hx0, hx0, mul_zero]
    exact hasSum_zero
  · have hw := h1 hx0
    letI : MeasurableSpace (GU σ n) := borel _
    haveI : BorelSpace (GU σ n) := ⟨rfl⟩
    obtain ⟨μ, hμH, hμK⟩ := GlobalTheory.ZetaSumU.exists_haar (ϖ : L) hU n
    have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1
    obtain ⟨hint, -, hval⟩ := (hD L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α _ hw).1 (hdom hx0)
    have hval' := hval m hm
    have hF : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) * (ℓ (ρ (g * k) x) / ℓ x) =
        Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x) := fun g k hk => by
      have h2 := hw.1 1 ⟨k, hk⟩ g
      simp only [OneMemClass.coe_one, one_mul] at h2
      rw [hright g k hk, h2]
    have hs := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ hF hint).of_norm
    have hci := (GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) hKo hμK
      (fun g => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x)) _ hF hs.hasSum).2
    have hS := hs.hasSum
    rw [← hci, hval'] at hS
    have h3 := hS.mul_right (ℓ x)
    simpa only [mul_assoc, div_mul_cancel₀ _ hx0] using h3

end GlobalTheory.DoublingSumU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LvTwDivDvInertEqStdL

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem LvTw_div_dv_inert_eq_stdL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (α : Fin (r / 2) → ℂˣ) (s : ℂ), Module.finrank F E = 2 → IsInertAt F E v w → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → B w = bcParam r α → LvTw B m v (s + 1 / 2) / dv E r b v s = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (qV F v) r α (((m w)⁻¹ : ℂˣ) : ℂ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (qV F v) r b s := by
  intro F E _ _ _ _ _ B m v w r b α s h2 hw hU hB
  have hv := InertChart.under_eq_iff hw
  have hq := InertChart.absNorm_eq h2 hw
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (one_lt_absNorm v).ne_bot
  have hns := not_isSplit_of_isInertAt hw
  rw [LvTw_inert B m hv hq, hB]
  congr 1
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL, Units.val_inv_eq_inv_val]
    congr 2
    rw [npow, show qV F v = Ideal.absNorm v.asIdeal from rfl, pow_two,
      show -(2 * (s + 1 / 2)) = -(s + 1 / 2) + -(s + 1 / 2) by ring, Complex.cpow_add _ _ hq0,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  · rw [dv, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [locL, etaFam_of_unram hU, eulerFac_singleton, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.etaL, Units.val_pow_eq_pow_val, npow,
      show qV F v = Ideal.absNorm v.asIdeal from rfl]
    have he : ((etaU E v : ℂˣ) : ℂ) = -1 := by simp [etaU, hns]
    rw [he]

end GlobalTheory.LFun
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.LocZetaInertAd

theorem domain_of_bound {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (α : Fin (n / 2) → ℂˣ) {ε : ℂ} (hε : ‖ε‖ = 1) {s : ℂ}
    (hs : (n : ℝ) < s.re) (hα : ∀ i, ‖((α i : ℂˣ) : ℂ)‖ ≤ ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2) ∧
      ‖(((α i)⁻¹ : ℂˣ) : ℂ)‖ ≤ ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q ε s) α := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hy : ‖GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q ε s‖ = (q : ℝ) ^ (-(2 * s.re + 1)) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY, norm_mul, hε, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 1
    simp
  have hQ : ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2) = (q : ℝ) ^ (n : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_mul hq0.le]
    congr 1; push_cast; ring
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have key : (q : ℝ) ^ (-(2 * s.re + 1)) * (q : ℝ) ^ (n : ℝ) < 1 := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-(2 * s.re + 1)) := (Real.rpow_pos_of_pos hq0 _).le
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hy]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  · rw [hy]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((hα i).1.trans hQ.le) hpos) key
  · rw [hy]
    have := (hα i).2
    rw [Units.val_inv_eq_inv_val, norm_inv] at this
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (this.trans hQ.le) hpos) key

end GlobalTheory.LocZetaInertAd

namespace GlobalTheory.LocZetaInertAd


theorem localZetaOn_inert : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D (fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → LocalZetaOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro hU D hPB A L hL χ b hχ hRes v hv hunr μ hμ hμK s hs φ hφ par c hc
  classical
  have hcm := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hc' := hc
  obtain ⟨-, V, _, _, ρ, x, ℓ, hpar, hℓ, hcx⟩ := hc'
  have hfix := (hpar w h).mem_fixed
  rcases hpar w h with ⟨hsplit, -⟩ | ⟨hw, c', ϖ0, e, α, hUI, he, hsat, hBw⟩
  · exact absurd hsplit hv
  have hϖ0 : ϖ0 ≠ 0 := by
    intro h0
    have := hUI.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let ϖ : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ0 hϖ0
  obtain ⟨hUnr, hχϖ, hχϖb, Φ, hΦ, hφΦ⟩ := GlobalTheory.KerInert.sphSec_inert D A L hL χ b hRes v w h hw (hunr w h) s φ hφ c' ϖ e hUI he
  let ρ' : Representation ℂ (Formalism.UG.GU c' A.rank) V := ρ.comp e.symm.toMonoidHom
  have hℓ' : ∀ k ∈ Formalism.UG.KU c' A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x) := by
    intro k hk g
    have hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v := (he.2.2 _).2 (by simpa using hk)
    have := hℓ _ hk' (e.symm g)
    simpa [ρ'] using this
  have hdom : ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain
      (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY (Formalism.UG.qV D.host.F v) (GlobalTheory.LFun.locChar χ⁻¹ w ϖ) s) α := by
    intro hx0
    have hc1 : c 1 ≠ 0 := by rw [hcx, map_one, one_apply_eq_self]; exact hx0
    obtain ⟨-, hbd⟩ := hPB A L hL v hv par c hc hc1 w h
    have hN : Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v ^ 2 := GlobalTheory.LFun.InertChart.absNorm_eq h2 hw
    have hq : 2 ≤ Formalism.UG.qV D.host.F v := hUI.2.2.2.2.2.1
    refine GlobalTheory.LocZetaInertAd.domain_of_bound hq α (GlobalTheory.LFun.norm_locChar _ _ _) (by exact_mod_cast hs) fun i => ?_
    have h1 := hbd (α i) (by rw [hBw]; simp [GlobalTheory.LGrp.bcParam])
    have h3 := hbd (α i)⁻¹ (by rw [hBw]; simp [GlobalTheory.LGrp.bcParam])
    rw [hN] at h1 h3
    exact ⟨h1, h3⟩
  obtain ⟨hΦK, hsum⟩ := GlobalTheory.DoublingSumU.hasSum_doubling_inert hU (w.adicCompletion D.host.E) ϖ c' (Formalism.UG.qV D.host.F v) A.rank hUI
    (GlobalTheory.LFun.locChar χ⁻¹ w) hUnr b hχϖb s Φ hΦ V ρ' x α hsat ℓ hℓ' hdom
  have hsum' : HasSum (fun a : Gv A v ⧸ stabLoc D.sp.cm.sig A.gram L v =>
      φ (ioAt A v a.out) * c a.out)
      (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (Formalism.UG.qV D.host.F v) A.rank α (GlobalTheory.LFun.locChar χ⁻¹ w ϖ) (s + 1 / 2) /
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (Formalism.UG.qV D.host.F v) A.rank b s * ℓ x) := by
    refine GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient _ _ e _ _ he.2.2 (fun g => φ (ioAt A v g) * c g) ?_ _ ?_
    · intro g k hk
      show φ (ioAt A v (g * k)) * c (g * k) = φ (ioAt A v g) * c g
      rw [hφΦ, hφΦ, map_mul, hΦK _ _ ((he.2.2 k).1 hk), hcx, hcx, map_mul, mul_apply_eq_comp,
        GlobalTheory.LGrp.mem_fixed.1 hfix k hk]
    · have hfun : ∀ a : Formalism.UG.GU c' A.rank ⧸ Formalism.UG.KU c' A.rank, φ (ioAt A v (e.symm a.out)) * c (e.symm a.out) =
          Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c' A.rank a.out) * ℓ (ρ' a.out x) := fun a => by
        rw [hφΦ, hcx, MulEquiv.apply_symm_apply]; rfl
      simp only [hfun]
      exact hsum
  have : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  obtain ⟨hint, hval⟩ := GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets (Gv A v) μ (stabLoc D.sp.cm.sig A.gram L v) (isOpen_stabLoc _ _ _ v) hμK
    (fun g => φ (ioAt A v g) * c g) _ (fun g k hk => by
      show φ (ioAt A v (g * k)) * c (g * k) = φ (ioAt A v g) * c g
      rw [hφΦ, hφΦ, map_mul, hΦK _ _ ((he.2.2 k).1 hk), hcx, hcx, map_mul, mul_apply_eq_comp,
        GlobalTheory.LGrp.mem_fixed.1 hfix k hk]) hsum'
  refine ⟨hint, ?_⟩
  rw [hval, GlobalTheory.LFun.LvTw_div_dv_inert_eq_stdL _ _ par (GlobalTheory.LFun.val χ) v w A.rank b α s h2 hw (GlobalTheory.LFun.isUnram_of_isInertAt hw) hBw, ← hχϖ,
    hcx 1, map_one, one_apply_eq_self]

end GlobalTheory.LocZetaInertAd
end
end

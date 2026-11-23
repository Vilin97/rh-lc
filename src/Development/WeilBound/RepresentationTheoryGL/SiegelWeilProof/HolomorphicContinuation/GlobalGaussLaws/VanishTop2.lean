module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAutomorphicOfConvergence
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
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExistsStatement
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopologyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExistsStatement
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenCoreTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TwoSided
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.NullIff
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Wtc
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.LcOf

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAutomorphicOfConvergenceStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_automorphic_of_convergence : GlobalTheory.Published.WeilThetaConvergence → PositivityTheory.PfSWUS.ThetaAuto := by
  first | exact @GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto | exact GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto | (intros; apply GlobalTheory.CompanionTheory.ThetaAutoPf.thetaAuto <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimate

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.FarSeries

open PositivityTheory.RgEis PositivityTheory.Rg.SwEis Topology

theorem exp_mul_le {a b x s t L : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) (hL : |s - t| ≤ L) :
    Real.exp (x * s) ≤ Real.exp ((|a| + |b|) * L) * (Real.exp (a * t) + Real.exp (b * t)) := by
  have hx : |x| ≤ |a| + |b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, abs_nonneg b]
    · linarith [le_abs_self b, abs_nonneg a]
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  have h3 : x * (s - t) ≤ (|a| + |b|) * L :=
    calc x * (s - t) ≤ |x * (s - t)| := le_abs_self _
      _ = |x| * |s - t| := abs_mul _ _
      _ ≤ (|a| + |b|) * L := mul_le_mul hx hL (abs_nonneg _) (by positivity)
  have h4 : Real.exp (x * t) ≤ Real.exp (a * t) + Real.exp (b * t) := by
    rcases le_total 0 t with ht | ht
    · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h2 ht)
      linarith [Real.exp_pos (a * t)]
    · have := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right h1 ht)
      linarith [Real.exp_pos (b * t)]
  calc Real.exp (x * s) = Real.exp (x * (s - t)) * Real.exp (x * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ _ := mul_le_mul (Real.exp_le_exp.2 h3) h4 (Real.exp_pos _).le (Real.exp_pos _).le

theorem summable_along {G G' : Type} [Group G] [Group G'] [TopologicalSpace G'] (Φ : G ≃* G') (Γ P : Subgroup G) (Γ' K' P' : Subgroup G')
    (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (η : G' → ℝ) (hη : IsHt Γ' K' P' η) (x : ℝ)
    (hc : Conv Γ' P' fun g => x * η g) : Summable fun q : Cos P Γ => Real.exp (x * η (Φ (rep q))) := by
  let T : G' → ℂ := fun y => (Real.exp (x * η y) : ℂ)
  have hT : GlobalTheory.AutomorphicL2Unitary.LeftInv (P' ⊓ Γ') T := fun γ hγ y => by
    simp only [T, hη.left γ hγ.1 y, hη.rat γ hγ.2 hγ.1, zero_add]
  obtain ⟨-, h⟩ := GlobalTheory.StdUnn.cosetSum_along_mulEquiv G G' Φ P Γ P' Γ' hP hΓ T 1 1 (fun g => T (Φ g))
    (fun g => by simp) hT
  have h1 : GlobalTheory.Eis.CosetConv P' Γ' T (Φ (1 * 1)) := by
    refine (hc (Φ (1 * 1))).congr fun q => ?_
    show _ = ‖((Real.exp (x * η (rep q * Φ (1 * 1))) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine ((h 1).1 h1).congr fun q => ?_
  show ‖((Real.exp (x * η (Φ (rep q * 1))) : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_one]

theorem bounded_of_law {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (Φ : G ≃ₜ* G')
    (P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (hK : IsCompact (K' : Set G')) (hPar : IsPar Γ' K' P' c)
    (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (f : G → ℂ) (hf : Continuous f) (hlaw : ∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image Φ.symm.continuous).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  obtain ⟨p, hp, k, hk, e⟩ := hPar.iwa (Φ x)
  have hx : x = Φ.symm p * Φ.symm k := by
    apply Φ.injective
    simp [e]
  have hq : Φ.symm p ∈ P := (hP _).2 (by simpa using hp)
  rw [hx, hlaw _ hq, Φ.apply_symm_apply, norm_mul, hPar.ch.norm p hp, one_mul]
  exact (hM _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)

theorem eFar : EFar := by
  intro hLip G G' _ _ _ _ _ _ _ _ Φ Γ P Γ' K' P' c η R hK hPar hη hΓ hP hcv f hf hlaw
  have hsum : ∀ x : ℝ, R < x → Summable fun q : Cos P Γ => Real.exp (x * η (Φ (rep q))) := fun x hx =>
    summable_along Φ.toMulEquiv Γ P Γ' K' P' hΓ hP η hη x (hcv x hx)
  obtain ⟨M, hM0, hM⟩ := bounded_of_law Φ P Γ' K' P' c hK hPar hP f hf hlaw
  have key : ∀ a b : ℝ, R < a → R < b → ∀ C : Set G, IsCompact C → ∃ u : Cos P Γ → ℝ, Summable u ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ∀ g ∈ C, ∀ q : Cos P Γ,
        ‖Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g)‖ ≤ u q := by
    intro a b ha hb C hC
    obtain ⟨L, hL⟩ := hLip G' Γ' K' P' η hK hPar.iwa hη (Φ '' C) (hC.image Φ.continuous)
    refine ⟨fun q => M * Real.exp ((|a| + |b|) * L) *
      (Real.exp (a * η (Φ (rep q))) + Real.exp (b * η (Φ (rep q)))), ((hsum a ha).add (hsum b hb)).mul_left _, ?_⟩
    intro z h1 h2 g hg q
    have h3 := exp_mul_le (s := η (Φ (rep q * g))) (t := η (Φ (rep q))) (L := L) h1 h2
      (by rw [map_mul]; exact hL _ _ ⟨g, hg, rfl⟩)
    have h4 : (z * (η (Φ (rep q * g)) : ℂ)).re = z.re * η (Φ (rep q * g)) := by simp
    rw [norm_mul, Complex.norm_exp, h4]
    calc _ ≤ (Real.exp ((|a| + |b|) * L) * (Real.exp (a * η (Φ (rep q))) + Real.exp (b * η (Φ (rep q))))) * M :=
          mul_le_mul h3 (hM _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hcont : ∀ q : Cos P Γ, Continuous fun y : ℂ × G =>
      Complex.exp (y.1 * η (Φ (rep q * y.2))) * f (rep q * y.2) := fun q => by
    have h1 : Continuous fun y : ℂ × G => rep q * y.2 := continuous_const.mul continuous_snd
    have h2 : Continuous fun y : ℂ × G => ((η (Φ (rep q * y.2)) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hη.cont.comp (Φ.continuous.comp h1))
    exact (Complex.continuous_exp.comp (continuous_fst.mul h2)).mul (hf.comp h1)
  have hopen : ∀ a b : ℝ, IsOpen {z : ℂ | a < z.re ∧ z.re < b} := fun a b =>
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hab : ∀ z : ℂ, R < z.re → R < (R + z.re) / 2 ∧ R < z.re + 1 ∧ z ∈ {w : ℂ | (R + z.re) / 2 < w.re ∧ w.re < z.re + 1} :=
    fun z hz => ⟨by linarith, by linarith, by show _ ∧ _; constructor <;> linarith⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz C hC
    obtain ⟨u, hu, hb⟩ := key z.re z.re hz hz C hC
    exact ⟨u, hu, fun g hg q => hb z le_rfl le_rfl g hg q⟩
  · intro g z₀ hz₀
    obtain ⟨h1, h2, h3⟩ := hab z₀ hz₀
    obtain ⟨u, hu, hb⟩ := key _ _ h1 h2 {g} isCompact_singleton
    have hd : DifferentiableOn ℂ (fun z => ∑' q : Cos P Γ, Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g))
        {w : ℂ | (R + z₀.re) / 2 < w.re ∧ w.re < z₀.re + 1} := by
      refine Complex.differentiableOn_tsum_of_summable_norm hu (fun q => ?_) (hopen _ _)
        (fun q w hw => hb w hw.1.le hw.2.le g rfl q)
      have : Differentiable ℂ fun z : ℂ => Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g) := by fun_prop
      exact this.differentiableOn
    exact (hd.differentiableAt ((hopen _ _).mem_nhds h3)).differentiableWithinAt
  · rintro ⟨z₀, g₀⟩ ⟨hz₀, -⟩
    obtain ⟨h1, h2, h3⟩ := hab z₀ hz₀
    obtain ⟨C', hC'c, hC'm⟩ := exists_compact_mem_nhds (Φ g₀)
    have hCm : Φ.symm '' C' ∈ 𝓝 g₀ := Filter.mem_of_superset (Φ.continuous.continuousAt.preimage_mem_nhds hC'm)
      fun x hx => ⟨Φ x, hx, by simp⟩
    obtain ⟨u, hu, hb⟩ := key _ _ h1 h2 _ (hC'c.image Φ.symm.continuous)
    have hd : ContinuousOn (fun y : ℂ × G => ∑' q : Cos P Γ, Complex.exp (y.1 * η (Φ (rep q * y.2))) * f (rep q * y.2))
        ({w : ℂ | (R + z₀.re) / 2 < w.re ∧ w.re < z₀.re + 1} ×ˢ (Φ.symm '' C')) :=
      continuousOn_tsum (fun q => (hcont q).continuousOn) hu
        fun q y hy => hb y.1 hy.1.1.le hy.1.2.le y.2 hy.2 q
    exact (hd.continuousAt (prod_mem_nhds ((hopen _ _).mem_nhds h3) hCm)).continuousWithinAt
  · intro z γ hγ g
    refine GlobalTheory.Eis.leftInv_cosetSum (fun δ hδ x => ?_) γ hγ g
    have h1 : Φ δ ∈ P' := (hP δ).1 hδ.1
    have h2 : Φ δ ∈ Γ' := (hΓ δ).1 hδ.2
    simp only [hlaw δ hδ.1 x, map_mul, hη.left _ h1, hη.rat _ h2 h1, hPar.ch.rat _ h2 h1, zero_add, one_mul]

end GlobalTheory.CompanionTheory.FarSeries

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimateStatement

section

@[expose] public section

open PositivityTheory.Rg.SwEis

theorem _root_.GlobalTheory.T.eisenstein_far_estimate : EFar := by
  first | exact @GlobalTheory.CompanionTheory.FarSeries.eFar | exact GlobalTheory.CompanionTheory.FarSeries.eFar | (intros; apply GlobalTheory.CompanionTheory.FarSeries.eFar <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimate

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr PositivityTheory.Rg.SwEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwEisIwa

theorem iwa_of_rank (hC : Chart) (D : D7) (χ : (AE D)ˣ →* Circle) (V : HSp D) :
    Iwa ((adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin V.rank))) ((adCM D.sp.cm.sig χ).uK (-1) (Fin V.rank)) := by
  obtain ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj V
  obtain ⟨Φ, p, -, hQ, hK, -, -⟩ := hC D χ V a ha
  intro g
  obtain ⟨q, k, hk, hqk⟩ := (GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha)).1
    (Φ.symm g * (p : GA D (dblSp V))⁻¹)
  refine ⟨Φ ((q : GA D (dblSp V)) * p), (hQ _).1 (Subgroup.mul_mem _ q.2 p.2),
    Φ ((p : GA D (dblSp V))⁻¹ * k * p), (hK k).1 hk, ?_⟩
  have h1 : Φ.symm g = (q : GA D (dblSp V)) * k * p := by
    rw [← hqk, inv_mul_cancel_right]
  have h2 : (q : GA D (dblSp V)) * p * ((p : GA D (dblSp V))⁻¹ * k * p) = (q : GA D (dblSp V)) * k * p := by
    group
  rw [← map_mul, h2, ← h1]
  exact (Φ.apply_symm_apply g).symm

theorem eIwa : EIwa := fun hC D χ n =>
  iwa_of_rank hC D χ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n)

end GlobalTheory.CompanionTheory.SwEisIwa

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimateStatement

section

@[expose] public section

open PositivityTheory.Rg.SwEis

theorem _root_.GlobalTheory.T.eisenstein_iwasawa_estimate : EIwa := by
  first | exact @GlobalTheory.CompanionTheory.SwEisIwa.eIwa | exact GlobalTheory.CompanionTheory.SwEisIwa.eIwa | (intros; apply GlobalTheory.CompanionTheory.SwEisIwa.eIwa <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.StrongEisensteinBounds.Strong

section

@[expose] public section

namespace PositivityTheory.Rg.SwEis.Hd

open PositivityTheory.RgEis.Hd

theorem eisStrong : PositivityTheory.Rg.Sw.Glob.EisStrong :=
  GlobalTheory.T.eisenstein_topology dict dictInf (cmGood_of stdGood dict dictInf) grpTop bdetLaw extLaw (parLaw_of bdetLaw extLaw grpTop)
    sgAll GlobalTheory.T.standard_section_exists (GlobalTheory.T.eisenstein_iwasawa_estimate (GlobalTheory.T.chart_section_exists dict dictInf GlobalTheory.T.standard_section_exists)) (GlobalTheory.T.scalar_section_exists secLaw (wallLaw_of secLaw))
    (GlobalTheory.T.eisenstein_far_estimate htLip) GlobalTheory.T.eisenstein_gluing

end PositivityTheory.Rg.SwEis.Hd
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop2

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem absThm : AbsThm := AbsSt.absThm_of lv (cyc_of fft) (lc_of fft) nullIff

theorem top2 (hLF : LocFact) (hAA : AwayAct) (hLi : LocInst) (hTA : PositivityTheory.PfSWUS.ThetaAuto) (hLC : LieComm)
    (hDO : DerivOne) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top absThm hLF hAA hLi hTA hLC hDO hId PositivityTheory.Rg.SwEis.Hd.eisStrong hC wtc

theorem top3 (hLF : LocFact) (hAA : AwayAct) (hLi : LocInst) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil)
    (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top2 hLF hAA hLi (GlobalTheory.T.theta_automorphic_of_convergence wtc) hLC hDO hId hC

end PositivityTheory.Rg.Sw.Glob
end
end

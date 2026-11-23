module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitAtCOneIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.HolValueAtConstMulCpow
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.DictAsm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GramZeroLeft
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Height
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SectionLinearFinsetSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasHermTop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelExOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThGramIncM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.PureGenSubFock

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.CoreX

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem coreX : CoreX := by
  intro ok vac c hT hA hS hU hW hD F E _ _ _ _ _ σ d R hok hE Φ hΦ P gf hpg hv x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨dd, J, T', bs, ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c', C, hDat, hAn, ⟨e, he⟩, hC, ⟨t, ht⟩,
    μH, 𝓕, hH, hF, horb⟩ := hD hT hA F E σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t', ht'⟩ := hU F E σ d (s0 d.m d.n) (d.sec0 Φ) (hS F E σ d Φ hΦ) (hE Φ hΦ)
  have hG := hW F E σ d.m d.n dd J T' bs ψ (InfinitePlace F) θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν hDat hok
    (Or.inr hAn) (fun h => ⟨fun i => congrFun (hv h) i, e, he⟩)
    ⟨max t t', fun z hz => (ht z (lt_of_le_of_lt (le_max_left _ _) hz)).1
      ((ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hcd ε w hw x).1)⟩ μH 𝓕 hH hF
  rw [horb, mul_left_comm]
  exact ((holValueAt_const_mul_cpow c' hC (s0 d.m d.n)).mul hG).congr ⟨t, fun z hz => ((ht z hz).2).symm⟩

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IwaRedOfC

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem kFinK : KFinK := fun _ _ _ _ _ _ _ _ d Φ hΦ k hk => kfin_om d hΦ hk

theorem iwaRedC : IwaRedC := by
  intro hT c F E _ _ _ _ _ σ d Q hQs hQK hL Φ hΦ x nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := par_decomp d p t hp
  have key := hL (d.om k Φ) (hQK Φ hΦ k hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
    funext z
    rw [← int_n d nb lam 𝓖 hcd T w n0 m0 β₀ hn]
    congr 1
    funext β
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc]]
    simp only [flat, a_mul_K d _ k hk, section_mul_weil_action]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact orb_n hT d T (om_mem_sch d _ (om_mem_sch d _ (hQs Φ hΦ))) n0 β₀ hn
  show HolValueAt _ _ _
  rw [e1, e2, mul_left_comm]
  exact holValueAt_const_mul _ key

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.LinRedC

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem linRedC : LinRedC := by
  unfold LinRedC
  intro hT hTC hL hU hS c F E _ _ _ _ _ σ d hE k cs Φs hK x hW
  have hTT : TTheta := hT.2.2.2.1
  have hTA : ThetaAuto := hT.2.2.2.2
  have hsch : ∀ i, Φs i ∈ d.sch := fun i => (hK i).1
  have hΦ : (∑ i : Fin k, cs i • Φs i) ∈ d.sch :=
    lin_sum_mem d Finset.univ cs Φs (fun i _ => hsch i)
  have hunf := fun i => hU F E σ d (s0 d.m d.n) (d.sec0 (Φs i)) (hS F E σ d (Φs i) (hK i)) (hE (Φs i) (hK i))
  choose t ht using hunf
  have hpsi : ∀ a, ‖d.B.ψ a‖ = 1 := fun a => GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std a
  unfold WhitAtC
  intro nb lam 𝓖 hcd ε w hw T hT'
  have hval : c * d.orb T ((d.om x) (∑ i : Fin k, cs i • Φs i)) =
      ∑ i : Fin k, cs i * (c * d.orb T ((d.om x) (Φs i))) := by
    have hI : d.I (∑ i : Fin k, cs i • Φs i) = ∑ i : Fin k, cs i • d.I (Φs i) := by
      funext y
      rw [lin_I_sum d hTT hTA Finset.univ cs Φs (fun i _ => hsch i) y]
      simp [Finset.sum_apply]
    have h1 := hTC F E σ d _ hΦ nb lam 𝓖 hcd T x
    rw [← h1, hI, lin_fc_sum hL d hcd T hT' x Finset.univ cs (fun i => d.I (Φs i))
      (fun i => ((hTA F E σ d).2.2 (Φs i) (hsch i)).2.1)
      (fun i => ((hTA F E σ d).2.2 (Φs i) (hsch i)).2.2), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hTC F E σ d _ (hsch i) nb lam 𝓖 hcd T x]
    ring
  rw [hval]
  have hsum := lin_holValueAt_sum Finset.univ cs
    (fun i z => ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (↑↑T * ↑β)) ∂lam)
    (fun i => c * d.orb T ((d.om x) (Φs i))) (s0 d.m d.n)
    (fun i _ => hW i nb lam 𝓖 hcd ε w hw T hT')
  refine HolValueAt.congr hsum ⟨∑ i : Fin k, |t i|, fun z hz => ?_⟩
  have hz' : ∀ i, t i < z.re := fun i =>
    lt_of_le_of_lt ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |t j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))) hz
  have hint : ∀ i, MeasureTheory.Integrable (fun β => flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (↑↑T * ↑β))) lam := fun i =>
    ((ht i z (hz' i) nb lam 𝓖 hcd ε w hw x).1).mul_bdd
      (lin_psi_meas d _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun β => (hpsi _).le))
  simp only
  simp_rw [← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_finsetSum]
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun β => ?_))
    simp only [flat, section_linear_finset_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · exact fun i _ => (hint i).const_mul (cs i)

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.VacIsPureBy

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def vac_gen {d : SD σ} (R : RD d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ φ, Dense.Good φ ∧ f = genF R (fun _ => 1) (Dense.pf φ)}

theorem vac_gen_sub {d : SD σ} (R : RD d) : vac_gen R ⊆ R.vac := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨Dense.pf φ, Dense.pf_mem hφ, rfl⟩

theorem vac_le_span {d : SD σ} (R : RD d) : R.vac ≤ Submodule.span ℂ (vac_gen R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  have := Dense.mem_span_pf hg
  clear hg
  have key : genL R (fun _ => 1) g ∈ Submodule.span ℂ (vac_gen R) := by
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨φ, hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key

theorem vac_isPureBy {d : SD σ} (R : RD d)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = genF R (fun _ => 1) (Dense.pf φ)) : ∃ gf, IsPureBy R Φ (fun _ => 1) gf := by
  refine ⟨φ, fun v => hφ.1 v, hφ.2.mono fun v hv => hv, ?_⟩
  rw [h]
  rfl

theorem vacSpan : VacSpan := by
  intro hT hF hPK hVK F E _ _ _ _ _ σ d R Φ hΦ hTΦ
  have hB := hT.1 F E σ d
  have hvf : R.vac ≤ R.fock := (hVK F E σ d R).2.1
  have h1 : d.T Φ ∈ Submodule.span ℂ (vac_gen R) := vac_le_span R hTΦ
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 h1
  have hpre : ∀ i : Fin k, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) := fun i =>
    hB.2.1 _ ((hF F E σ d R).1 (hvf (vac_gen_sub R (gs i).2)))
  choose Φs hΦs hTs using hpre
  refine ⟨k, c, Φs, fun i => ⟨hPK F E σ d R (Φs i) (hΦs i) (hTs i ▸ hvf (vac_gen_sub R (gs i).2)),
    hTs i ▸ vac_gen_sub R (gs i).2, ?_⟩, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := (gs i).2
    exact vac_isPureBy R φ hφ (Φs i) ((hTs i).trans e)
  · have hmem : Φ - ∑ i, c i • Φs i ∈ d.sch :=
      sub_mem hΦ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i))
    have h0 : d.T (Φ - ∑ i, c i • Φs i) = 0 := by
      rw [T_sub, T_sum, ← hsum]
      simp only [hTs, sub_self]
    exact (sub_eq_zero.1 (hB.2.2 _ hmem h0))

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GenDictXOf

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem genDictX_of : GenDictX :=
  dictAsmX cellFormula relEx Ht.heightDict measDict thetaDict

theorem whitK_of (hT : TAll) (hA : AuxiliaryPrimeFunction) (hR : RDEx) (hF : FockMem) (hK : KFinPoly) (hS : SecK) (hU : Unfold) (hW : Gen.WhitGenLt)
    (hTC : ThetaCoef) (hLB : LamBd) (hPK : PolyKFin) : WhitK :=
  whitK_of_X iwaRedC pureSpan linRedC coreX genDictX_of kFinK hT hA hR hF hK hS hU hW hTC hLB hPK

theorem whitEq_of (hT : TAll) (hA : AuxiliaryPrimeFunction) (hR : RDEx) (hF : FockMem) (hK : KFinPoly) (hS : SecK) (hU : Unfold) (hEW : EisWk)
    (hW : Gen.WhitGenEq) (hTC : ThetaCoef) (hLB : LamBd) (hPK : PolyKFin) : WhitEq :=
  whitEq_of_X iwaRedC pureSpan linRedC coreX genDictX_of kFinK hT hA hR hF hK hS hU hEW hW hTC hLB hPK

theorem whitLow_of (hVK : VacK)
    (hT : TAll) (hA : AuxiliaryPrimeFunction) (hF : FockMem) (hS : SecK) (hU : Unfold) (hEW : EisWk) (hW : Gen.WhitGenLow)
    (hTC : ThetaCoef) (hLB : LamBd) (hPK : PolyKFin) : WhitLow :=
  whitLow_of_X iwaRedC vacSpan linRedC coreX genDictX_of hVK hT hA hF hS hU hEW hW hTC hLB hPK

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
end

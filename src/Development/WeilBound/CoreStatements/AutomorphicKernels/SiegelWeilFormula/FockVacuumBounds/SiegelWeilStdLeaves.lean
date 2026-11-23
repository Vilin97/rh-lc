module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.MajorantW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RdEx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.MeromorphicOnOfWeak
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.SecK
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Strong
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainLe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacDataOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.HolValueAtFinsum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.ThetaSumAdd
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacLin
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.FourierZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.LamSingOf
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.SiegelWeilStdLt

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.Khead

theorem siegelWeilStd_lt (h : SWStdLt) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) r s r' s', n < m → B.IsGood σ → 1 ≤ m → 1 ≤ n →
    min r s = 0 → (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
  intro F E _ _ _ _ _ σ B m n A Y r s r' s' hnm hgood hm hn hmin hsign χ hχ hres κ _ dd om S l hdbl b K a
    hfr hK ha μ D hμ hD Φ hΦ hfin
  have key := h F E σ B m n A Y r s r' s' χ κ dd om S l b K a μ D Φ
    ⟨hgood, hm, hn, hnm, hmin, hsign, hχ, hres, hdbl, hfr, hK, ha, hμ, hD, hΦ, hfin⟩
  have hEq : thetaMean om S μ D Φ =
      fun x => (if n < m then (1 : ℂ) else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
    funext x
    rw [if_pos hnm, one_mul]
    try rfl
  rw [hEq] at key
  exact key

end PositivityTheory.SiegelWeilFormula.Khead
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.FieldOf

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eisValue_of (hBL : EisBL) (hSec : SecK) (d : SD σ) {r' s' : ℕ}
    (hY : d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s') (c : ℂ) (hM : MainC c d) (Φ : d.Fn) (hK : d.KFin Φ) :
    EisValueAt (flat d.a (d.sec0 Φ) (s0 d.m d.n)) (s0 d.m d.n) (fun x => c * d.I Φ x) := by
  obtain ⟨Ê, ⟨t, hsum, -⟩, hw⟩ := hBL F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt (s0 d.m d.n) (d.sec0 Φ) (hSec F E σ d Φ hK)
  intro x
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ y) = flat d.a (d.sec0 Φ) (s0 d.m d.n) z :=
    fun z => funext fun y => by
      simp only [SD.Ht, flat]
      rw [Real.coe_toNNReal _ (Khead.hgt_nonneg d.ok.hgt y)]
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → d.eis (d.sec0 Φ) (s0 d.m d.n) z x = Ê z x := fun z hz => by
    simp only [SD.eis]
    rw [hfl z]
    exact (hsum z hz x).tsum_eq
  have hmer := Khead.meromorphicOn_of_weak hw x
  have hext : IsExtAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (Ê · x) :=
    ⟨Set.univ, trivial, isRightDomain_univ, hmer, t, fun z hz => (Heisenberg₂ z hz).symm⟩
  obtain ⟨H', hext', han, hval⟩ := hM Φ hK x
  have hev := hext'.eventuallyEq hext
  have hloc : Function.update (Ê · x) (s0 d.m d.n) (c * d.I Φ x) =ᶠ[𝓝 (s0 d.m d.n)] H' := by
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with z hz
    by_cases e : z = s0 d.m d.n
    · subst e; rw [Function.update_self]; exact hval.symm
    · rw [Function.update_of_ne e]; exact (hz e).symm
  refine ⟨Function.update (Ê · x) (s0 d.m d.n) (c * d.I Φ x), fun z _ => (hmer z trivial).update _ _,
    ⟨max t (s0 d.m d.n).re, fun z hz => ?_⟩, han.congr hloc.symm, Function.update_self _ _ _⟩
  have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hz2 : z ≠ s0 d.m d.n := fun e => by subst e; exact lt_irrefl _ (lt_of_le_of_lt (le_max_right _ _) hz)
  rw [Function.update_of_ne hz2]
  exact hsum z hz1 x

end PositivityTheory.SiegelWeilFormula.Atop

namespace PositivityTheory.SiegelWeilFormula

theorem Atop.fieldOf : FieldOf := by
  intro hBL hSec hLt hLe F E _ _ _ _ _ σ B m n A Y r s r' s' h1 h2 h3 h4 h5 χ h6 h7 κ _ dd om S l h8 b K a h9 h10 h11 μ D
    h12 h13 Φ h14 h15
  by_cases hlt : n < m
  · exact Khead.siegelWeilStd_lt hLt F E σ B m n A Y r s r' s' hlt h1 h2 h3 h4 h5 χ h6 h7 κ dd om S l h8 b K a h9 h10 h11
      μ D h12 h13 Φ h14 h15
  · simp only [if_neg hlt]
    let d : SD σ :=
      { B := B, m := m, n := n, A := A, Y := Y, r := r, s := s, χ := χ, κ := κ, dd := dd, om := om, S := S, l := l, b := b,
        K := K, a := a, μ := μ, D := D, bs := Khead.basis2 h1,
        ok := ⟨h1, h2, h3, h4, h5.imp (fun h => ⟨h.1, h.2.skew⟩) (fun h => ⟨h.1, h.2.herm⟩), h6, h7, h8, h9, h10, h11, h12,
          h13⟩ }
    have hY : d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s' := h5.elim (fun h => .inr h.2) (fun h => .inl h.2)
    exact Atop.eisValue_of hBL hSec d hY 2 (hLe F E σ d (not_lt.mp hlt)) Φ ⟨h14, h15⟩

end PositivityTheory.SiegelWeilFormula

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacCore

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

open PositivityTheory.SiegelWeilFormula.KMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem genAt (hG : AbsSt.GenCore) (c : ℂ) (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hFM : FockMem) (hLo : LocOpEx)
    (hLI : LocInst) (hGS : GSplit) (hGI : GIinv) (hGD : GIdil) (hPK : PolyKFin) (hSK : SecK) (hEW : EisWk)
    (d : SD σ) (R : RD d) (w : InfinitePlace F) {Ψ : Mx F E d.m d.n → ℂ} (hΨ : Ψ ∈ R.away w)
    {φ : PX d.m d.n →ₗ[ℂ] d.Fn} (hφ : R.IsLift w Ψ φ)
    (hvac : ∀ x, HolValueAt (fun z => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ 1) x))
    (P : PX d.m d.n) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (φ P)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ P) x) := by
  have hEA := eisAll_of hSK hEW d
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  obtain ⟨L, hL⟩ := hLo F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P =>
    hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := by
    intro k hk P
    have h1 := (hL k (fP P) (isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    have hmem : d.om (R.ι w k) (φ P) - φ (ρ k P) ∈ d.sch := d.sch.sub_mem (om_mem d _ (hφ P).1) (hφ _).1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ hmem ?_)
    rw [← Tl_apply, map_sub, Tl_apply, Tl_apply, h1, (hφ _).2, sub_self]
  let Il : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) :=
    { toFun := fun P => c • d.I (φ P)
      map_add' := fun P Q => by rw [map_add (f := _), I_add d hTT hTA (hφ P).1 (hφ Q).1, smul_add]
      map_smul' := fun a P => by rw [map_smul, I_smul d hTT a (hφ P).1, RingHom.id_apply, smul_comm] }
  let sl : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) := (secl d).comp φ
  obtain ⟨-, -, hTG, hLC, hT2, hSC⟩ := hAux F E σ d
  have hE1 : d.Eis (d.sec0 (φ 1)) (s0 d.m d.n) := hEA (φ 1) (hKF 1)
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hE1 (s0 d.m d.n)
  have hCore : AbsSt.GlobCore (fun _ => true) (2 * Real.pi) sL ρ d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n)
      d.Ht sl Il :=
    { ιcont := R.cont w
      split := by
        intro g
        obtain ⟨x, y, c, r, hr, hg, hx⟩ := hGS F E σ d R w L hL Ψ hΨ φ hφ g
        refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hx y').1, fun P => ?_⟩⟩
        rw [hsL]
        exact (hx y').2 P
      Icont := by
        show Continuous (c • d.I (φ 1))
        exact ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.1.const_smul c
      Ileft := by
        intro γ hγ g
        show c * d.I (φ 1) (γ * g) = c * d.I (φ 1) g
        rw [((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.2 γ hγ g]
      Ik := by
        intro P g k hk
        show c * thetaMean d.om d.S d.μ d.D (φ P) (g * R.ι w k) = c * thetaMean d.om d.S d.μ d.D (φ (ρ k P)) g
        unfold thetaMean
        simp only [map_mul, Module.End.mul_apply, (hTT F E σ d (φ P) (hφ P).1).2, hom k hk P]
      Iinv := by
        intro g a b P
        show c * d.I (φ (hOp (fun _ => true) (2 * Real.pi) a b P)) g = 0
        rw [hGI F E σ d R w Ψ hΨ φ hφ g a b P, mul_zero]
      Idil := by
        intro g X a ha
        obtain ⟨U, H, hU, hR, hc, hH⟩ := hGD F E σ d R w Ψ hΨ φ hφ g X a ha
        refine ⟨U, fun y z => c * H y z, hU, hR, continuousOn_const.mul hc,
          fun y => ⟨(hH y).1.const_mul c, fun t => ?_, fun r => ?_⟩⟩
        · show c * H y t = c * d.I (φ 1) (g * R.ι w (y * a t))
          rw [(hH y).2.1 t]
        · show iteratedDeriv r (fun z => c * H y z) 0 = c * d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y)
          rw [iteratedDeriv_const_mul' c r (H y)]
          show c * iteratedDeriv r (H y) 0 = _
          rw [(hH y).2.2 r]
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ }
  have hVac : AbsSt.VacData (par2 σ d.Y) (rat2 σ d.Y) (s0 d.m d.n) d.Ht sl Il := by
    obtain ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩ := vacData_of (fun z g => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z g)
      (s0 d.m d.n) (fun g => c * d.I (φ 1) g) U pp Ê t hUo hRD hs0 hp hhol hcont (fun z hz g => (hconv z hz).2 g)
      hvac
    exact ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩
  exact hG d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD
    d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht sl Il hCore hVac P x

end PositivityTheory.SiegelWeilFormula.Atop

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacAll

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

open PositivityTheory.SiegelWeilFormula.KMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def _root_.PositivityTheory.SiegelWeilFormula.RD.gens {d : SD σ} (R : RD d) (s : Finset (InfinitePlace F)) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ), (∀ w ∉ s, P w = 1) ∧ g ∈ SB _ ∧
    f = fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2}

def _root_.PositivityTheory.SiegelWeilFormula.RD.vacOn {d : SD σ} (R : RD d) (s : Finset (InfinitePlace F)) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ (R.gens s)

theorem vacOn_empty_le {d : SD σ} (R : RD d) : R.vacOn ∅ ≤ R.vac := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hP, hg, rfl⟩
  refine Submodule.subset_span ⟨g, hg, ?_⟩
  funext X
  simp only [hP _ (Finset.notMem_empty _)]

theorem fock_le_vacOn_univ {d : SD σ} (R : RD d) : R.fock ≤ R.vacOn Finset.univ := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hg, rfl⟩
  exact Submodule.subset_span ⟨P, g, fun w hw => absurd (Finset.mem_univ w) hw, hg, rfl⟩

theorem vacOn_step (hG : AbsSt.GenCore) (c : ℂ) (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hFM : FockMem) (hLE : LiftEx)
    (hLo : LocOpEx) (hLI : LocInst) (hGS : GSplit) (hGI : GIinv) (hGD : GIdil) (hPK : PolyKFin) (hSK : SecK)
    (hEW : EisWk) (d : SD σ) (R : RD d) (w : InfinitePlace F) (s : Finset (InfinitePlace F)) (hw : w ∉ s)
    (ih : ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn s → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn (insert w s) → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x) := by
  have hgen : ∀ f ∈ R.gens (insert w s), ∃ Φf : d.Fn, d.KFin Φf ∧ d.T Φf = f ∧ ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φf) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φf x) := by
    rintro f ⟨P, g, hP, hg, rfl⟩
    set Ψ : Mx F E d.m d.n → ℂ := fun X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) *
      g fun k => (d.crd X k).2 with hΨdef
    have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨P, g, hg, rfl⟩
    obtain ⟨φ, hφ⟩ := hLE F E σ d R w Ψ hΨ
    have hTP : ∀ Q : PX d.m d.n, d.T (φ Q) = fun X => (∏ w', fP (Function.update P w Q w') (R.loc w' X)) *
        g fun k => (d.crd X k).2 := by
      intro Q
      rw [(hφ Q).2]
      funext X
      simp only [RD.tens, hΨdef]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun w' hw' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
    have hfock : ∀ Q, d.T (φ Q) ∈ R.fock := fun Q => by
      rw [hTP Q]
      exact Submodule.subset_span ⟨_, g, hg, rfl⟩
    have hKF : ∀ Q, d.KFin (φ Q) := fun Q => hPK F E σ d R (φ Q) (hφ Q).1 (hfock Q)
    have hvac : ∀ x, HolValueAt (fun z => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ 1) x) := by
      refine ih (φ 1) (hφ 1).1 ?_
      rw [hTP 1]
      refine Submodule.subset_span ⟨Function.update P w 1, g, fun w' hw' => ?_, hg, rfl⟩
      by_cases e : w' = w
      · subst e; exact Function.update_self _ _ _
      · rw [Function.update_of_ne e]
        exact hP w' (by simp [e, hw'])
    refine ⟨φ (P w), hKF (P w), ?_, genAt hG c hT hAux hFM hLo hLI hGS hGI hGD hPK hSK hEW d R w hΨ hφ hvac (P w)⟩
    rw [hTP (P w), Function.update_eq_self]
  intro Φ hΦ hTΦ x
  obtain ⟨k, a, f, hf⟩ := Submodule.mem_span_set'.1 hTΦ
  choose Φf hK hTf hI using fun i => hgen (f i).1 (f i).2
  have hΦeq : Φ = ∑ i, a i • Φf i := by
    have hmem : Φ - ∑ i, a i • Φf i ∈ d.sch :=
      d.sch.sub_mem hΦ (d.sch.sum_mem fun i _ => d.sch.smul_mem _ (hK i).1)
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ hmem ?_)

    rw [← Tl_apply, map_sub, map_sum]
    simp only [map_smul, Tl_apply, hTf, hf, sub_self]
  rw [hΦeq]
  exact ident_lincomb hT hSK hEW d c a Φf hK hI x

end PositivityTheory.SiegelWeilFormula.Atop

namespace PositivityTheory.SiegelWeilFormula

def VacAllOfC : Prop :=
  AbsSt.GenCore → TAll → AuxiliaryPrimeFunction → FockMem → LiftEx → LocOpEx → LocInst → GSplit → GIinv → GIdil → KFinPoly → PolyKFin →
    SecK → EisWk → VacAll

theorem Atop.vacAllOfC : VacAllOfC := by
  intro hG hT hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW F E _ _ _ _ _ σ d R c hV Φ hΦ x
  have claim : ∀ s : Finset (InfinitePlace F), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn s → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun Φ hΦ hT x => hV Φ hΦ (Atop.vacOn_empty_le R hT) x
    | insert w s hw ih => exact Atop.vacOn_step hG c hT hAux hFM hLE hLo hLI hGS hGI hGD hPK hSK hEW d R w s hw ih
  exact claim Finset.univ Φ hΦ.1 (Atop.fock_le_vacOn_univ R (hKP F E σ d R Φ hΦ)) x

end PositivityTheory.SiegelWeilFormula

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.SiegelWeilStdLeaves

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

theorem Atop.siegelWeilStd_of (hA : AbsThm) (hT : TAll) (hTC : ThetaCoef) (hLo : LocOpEx) (hLI : LocInst)
    (hGS : GSplit) (hGI : GIinv) (hGD : GIdil) (hKP : KFinPoly) (hPK : PolyKFin) (hU : Unfold)
    (hW : WhitK) (hWE : WhitEq) (hG : AbsSt.GenCore) (hLD : LDEx) (hVK : VacK) (hSt : Step) :
    SiegelWeilStd := by
  have hBL : EisBL := PositivityTheory.RgEis.Hd.eisBL
  have hSK : SecK := Khead.secK
  have hAux : AuxiliaryPrimeFunction := kfour.auxEx
  have hRD : RDEx := Krd.rdEx
  have hFM : FockMem := KFock.fockMem
  have hLE : LiftEx := KFock.liftEx hT.1
  have hLB : LamBd := kfour.lamBd
  have hLS : LamSing := KSing.lamSing_of kfour.coefEx kfour.fourierZero Krd.denseW hAux
  have hEW : EisWk := Aeis.eisWk
  have hMain := KMain.mainOf hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hW
  have hLt := Khead.headOf hBL hSK (Khead.eisStrong_of hBL) hMain
  have hEq := Atop.mainEq_of hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hEW hWE
  have hVA := Atop.vacAllOfC hG hT hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW
  have hLe := Atop.mainLeOf hRD hLD hVK hPK hEq hSt hVA
  exact Atop.fieldOf hBL hSK hLt hLe

end PositivityTheory.SiegelWeilFormula

end
end
end

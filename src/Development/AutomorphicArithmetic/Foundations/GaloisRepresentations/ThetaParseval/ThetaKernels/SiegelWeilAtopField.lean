module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelMultOfK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisWk
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadHead
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SWStdLtK
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.MeromorphicOnOfWeak
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainLe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopVacAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourFZ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourLB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadHead
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadSecK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadStrong
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKmainLin
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.HolValueAtFinsum
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdDenseW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingTop

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadLt

section

@[expose] public section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.Khead
theorem siegelWeilStd_lt_k (h : _root_.PositivityTheory.SiegelWeilFormula.SWStdLt_k) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) r s r' s', n < m → _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n →
    min r s = 0 → (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
  intro F E _ _ _ _ _ σ B m n A Y r s r' s' hlt h1 h2 h3 h4 h5 χ h6 h7 κ _ dd om S l h8 b K a h9 h10 h11 μ D h12 h13 Φ h14 h15
  simp only [if_pos hlt, one_mul]
  exact h F E σ B m n A Y r s r' s' χ κ dd om S l b K a μ D Φ
    ⟨h1, h2, h3, hlt, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopFieldOf

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eisValue_of_k (hBL : _root_.GlobalTheory.ThK.Dbl.EisBL_k) (hSec : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {r' s' : ℕ}
    (hY : d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s') (c : ℂ) (hM : _root_.PositivityTheory.SiegelWeilFormula.MainC_k c d) (Φ : d.Fn) (hK : d.KFin Φ) :
    EisValueAt (flat d.a (d.sec0 Φ) (s0 d.m d.n)) (s0 d.m d.n) (fun x => c * d.I Φ x) := by
  obtain ⟨Ê, ⟨t, hsum, -⟩, hw⟩ := hBL F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt (s0 d.m d.n) (d.sec0 Φ) (hSec F E σ d Φ hK)
  intro x
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ y) = flat d.a (d.sec0 Φ) (s0 d.m d.n) z :=
    fun z => funext fun y => by
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, flat]
      rw [Real.coe_toNNReal _ (Khead.hgt_nonneg d.ok.hgt y)]
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → d.eis (d.sec0 Φ) (s0 d.m d.n) z x = Ê z x := fun z hz => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis]
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
theorem Atop.fieldOf_k : _root_.PositivityTheory.SiegelWeilFormula.FieldOf_k := by
  intro hBL hSec hLt hLe F E _ _ _ _ _ σ B m n A Y r s r' s' h1 h2 h3 h4 h5 χ h6 h7 κ _ dd om S l h8 b K a h9 h10 h11 μ D
    h12 h13 Φ h14 h15
  by_cases hlt : n < m
  · exact _root_.PositivityTheory.SiegelWeilFormula.Khead.siegelWeilStd_lt_k hLt F E σ B m n A Y r s r' s' hlt h1 h2 h3 h4 h5 χ h6 h7 κ dd om S l h8 b K a h9 h10 h11
      μ D h12 h13 Φ h14 h15
  · simp only [if_neg hlt]
    let d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ :=
      { B := B, m := m, n := n, A := A, Y := Y, r := r, s := s, χ := χ, κ := κ, dd := dd, om := om, S := S, l := l, b := b,
        K := K, a := a, μ := μ, D := D, bs := _root_.PositivityTheory.SiegelWeilFormula.Khead.basis2_k h1,
        ok := ⟨h1, h2, h3, h4, h5.imp (fun h => ⟨h.1, h.2.skew⟩) (fun h => ⟨h.1, h.2.herm⟩), h6, h7, h8, h9, h10, h11, h12,
          h13⟩ }
    have hY : d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s' := h5.elim (fun h => .inr h.2) (fun h => .inl h.2)
    exact _root_.PositivityTheory.SiegelWeilFormula.Atop.eisValue_of_k hBL hSec d hY 2 (hLe F E σ d (not_lt.mp hlt)) Φ ⟨h14, h15⟩
end PositivityTheory.SiegelWeilFormula
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKmainMain

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem perLift_k (hA : AbsThm) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k)
    (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k)
    (hLS : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hW : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hnm : d.n < d.m) (hEA : d.EisAll) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (w : InfinitePlace F) {Ψ : Mx F E d.m d.n → ℂ} (hΨ : Ψ ∈ R.away w) {φ : PX d.m d.n →ₗ[ℂ] d.Fn}
    (hφ : R.IsLift w Ψ φ) (P : PX d.m d.n) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (φ P)) (s0 d.m d.n) z x) (s0 d.m d.n) (d.I (φ P) x) := by
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  obtain ⟨L, hL⟩ := hLo F E σ d R w
  obtain ⟨sL, ρ, p, q, e, hgood, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P =>
    hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := by
    intro k hk P
    have h1 := (hL k (fP P) (isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    have hmem : d.om (R.ι w k) (φ P) - φ (ρ k P) ∈ d.sch := d.sch.sub_mem (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d _ (hφ P).1) (hφ _).1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ hmem ?_)
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, h1, (hφ _).2, sub_self]
  let Il : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) :=
    { toFun := fun P => d.I (φ P)
      map_add' := fun P Q => by rw [map_add (f := _)]; exact _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hTT hTA (hφ P).1 (hφ Q).1
      map_smul' := fun a P => by rw [map_smul]; exact _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hTT a (hφ P).1 }
  let sl : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d).comp φ
  obtain ⟨-, ⟨ε, ww, hww, -⟩, hTG, hLC, hT2, hSC⟩ := hAux F E σ d
  have hsec1 : IsSec d.K d.χ (s0 d.m d.n) (d.sec0 (φ 1)) := hSK F E σ d (φ 1) (hKF 1)
  have hE1 : d.Eis (d.sec0 (φ 1)) (s0 d.m d.n) := hEA (φ 1) (hKF 1)
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hE1 (s0 d.m d.n)
  have hGDat : GlobData (fun _ => true) (2 * Real.pi) sL ρ d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht
      sl Il d.lamSet :=
    { ιcont := R.cont w
      split := by
        intro g
        obtain ⟨x, y, c, r, hr, hg, hx⟩ := hGS F E σ d R w L hL Ψ hΨ φ hφ g
        refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hx y').1, fun P => ?_⟩⟩
        rw [hsL]
        exact (hx y').2 P
      Icont := ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.1
      Ileft := ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.2
      Ik := by
        intro P g k hk
        show thetaMean d.om d.S d.μ d.D (φ P) (g * R.ι w k) = thetaMean d.om d.S d.μ d.D (φ (ρ k P)) g
        unfold thetaMean
        simp only [map_mul, Module.End.mul_apply, (hTT F E σ d (φ P) (hφ P).1).2, hom k hk P]
      Iinv := fun g a b P => hGI F E σ d R w Ψ hΨ φ hφ g a b P
      Idil := hGD F E σ d R w Ψ hΨ φ hφ
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩
      Λadd := fun l hl => (hLB F E σ d l hl).1
      Λbd := fun l hl => (hLB F E σ d l hl).2
      Λsing := fun f hf hinv hz => hLS F E σ d R w f hf hinv hz
      Λval := by
        rintro l ⟨nb, lam, 𝓖, T, x, hcd, hT, rfl⟩
        obtain ⟨t', ht'⟩ := hU F E σ d _ _ hsec1 hE1
        have hWh := hW F E σ d hnm hEA (φ 1) (hKF 1) nb lam 𝓖 hcd ε ww hww T hT x
        have hC := hTC F E σ d (φ 1) (hφ 1).1 nb lam 𝓖 hcd T x
        show HolValueAt (fun z => fc d.B.ψ d.b nb lam 𝓖 (d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z) T x) (s0 d.m d.n)
          (fc d.B.ψ d.b nb lam 𝓖 (d.I (φ 1)) T x)
        rw [hC]
        exact hWh.congr ⟨t', fun z hz => ((ht' z hz nb lam 𝓖 hcd ε ww hww x).2 T hT).symm⟩ }
  exact hA d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD (hgood hnm.le)
    d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht sl Il d.lamSet hGDat P x
theorem mainOf_k : _root_.PositivityTheory.SiegelWeilFormula.MainOf_k := by
  intro hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hW F E _ _ _ _ _ σ d hnm hEA Φ hΦ x
  obtain ⟨R⟩ := hRD F E σ d
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨k, P, Ψ, hΨ, hsum⟩ := (hFM F E σ d R).2.2 w _ (hKP F E σ d R Φ hΦ)
  choose φ hφ using fun i => hLE F E σ d R w (Ψ i) (hΨ i)
  have hsch : ∀ i, φ i (P i) ∈ d.sch := fun i => (hφ i (P i)).1
  have eT : ∀ i, d.T (φ i (P i)) = R.tens w (fP (P i)) (Ψ i) := fun i => (hφ i (P i)).2
  have hΦeq : Φ = ∑ i, φ i (P i) := by
    have hmem : Φ - ∑ i, φ i (P i) ∈ d.sch := d.sch.sub_mem hΦ.1 (d.sch.sum_mem fun i _ => hsch i)
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ hmem ?_)

    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, map_sum]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, eT, hsum, sub_self]
  have key : ∀ i, HolValueAt (fun z => d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x) (s0 d.m d.n)
      (d.I (φ i (P i)) x) := fun i =>
    _root_.PositivityTheory.SiegelWeilFormula.KMain.perLift_k hA hT hTC hAux hFM hLo hLI hGS hGI hGD hPK hSK hLB hLS hU hW d hnm hEA R w (hΨ i) (hφ i) (P i) x
  have hv : d.I Φ x = ∑ i, d.I (φ i (P i)) x := by
    rw [hΦeq, _root_.PositivityTheory.SiegelWeilFormula.KMain.I_sum_k d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => hsch i), Finset.sum_apply]
  have hKi : ∀ i, d.KFin (φ i (P i)) := fun i =>
    hPK F E σ d R _ (hsch i) (by rw [eT]; exact ((hFM F E σ d R).2.1 w (Ψ i) (hΨ i)).1 (P i))
  have hconv : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x := by
    intro i
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := hEA _ (hKi i) (s0 d.m d.n)
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hconv
  have hsec : d.sec0 Φ = fun y => ∑ i, d.sec0 (φ i (P i)) y := by
    funext y

    rw [hΦeq, ← _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_apply_k, map_sum, Finset.sum_apply]
    rfl
  have heq : EqRight (fun z => ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x)
      (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have := cosetSum_finsum (par2 σ d.Y) (rat2 σ d.Y) Finset.univ
      (fun i y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x (fun i _ => htt i z (hz' i))
    show ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x = d.eis (d.sec0 Φ) (s0 d.m d.n) z x
    rw [hsec]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.eis
    simp only [Finset.mul_sum]
    exact this.symm
  rw [hv]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq
end PositivityTheory.SiegelWeilFormula.KMain
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopField

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
theorem Atop.siegelWeilStd_of_k (hA : AbsThm) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k)
    (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hKP : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k)
    (hW : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k) (hWE : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k) (hG : AbsSt.GenCore) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k) (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k) (hSt : _root_.PositivityTheory.SiegelWeilFormula.Step_k) :
    _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k := by
  have hBL : _root_.GlobalTheory.ThK.Dbl.EisBL_k := _root_.PositivityTheory.RgEis.Hd.eisBL_k
  have hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k := _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k
  have hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties := _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds
  have hRD : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k := _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_k
  have hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
  have hLE : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_k hT.1
  have hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k := _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k
  have hLS : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k := _root_.PositivityTheory.SiegelWeilFormula.KSing.lamSing_of_k _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k _root_.PositivityTheory.SiegelWeilFormula.kfour.fourierZero_k _root_.PositivityTheory.SiegelWeilFormula.Krd.denseW_k hAux
  have hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k
  have hMain := _root_.PositivityTheory.SiegelWeilFormula.KMain.mainOf_k hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hW
  have hLt := _root_.PositivityTheory.SiegelWeilFormula.Khead.headOf_k hBL hSK (_root_.PositivityTheory.SiegelWeilFormula.Khead.eisStrong_of_k hBL) hMain
  have hEq := _root_.PositivityTheory.SiegelWeilFormula.Atop.mainEq_of_k hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hEW hWE
  have hVA := _root_.PositivityTheory.SiegelWeilFormula.Atop.vacAllOfC_k hG hT hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW
  have hLe := _root_.PositivityTheory.SiegelWeilFormula.Atop.mainLeOf_k hRD hLD hVK hPK hEq hSt hVA
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.fieldOf_k hBL hSK hLt hLe
end PositivityTheory.SiegelWeilFormula
end
end
end
end

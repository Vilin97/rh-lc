module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNearAt

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU.Approx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAtA_of_val {ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E} (hι : IsAdIso ι) (P : HeightOneSpectrum (𝓞 E))
    (z : AfE F E) (h : Valued.v (ι z P) ≤ 1) : IntAtA (F := F) P z := by
  classical
  set w := ι z with hw
  have hfin : Set.Finite {Q : HeightOneSpectrum (𝓞 E) | w Q ∉ Q.adicCompletionIntegers E} :=
    Filter.eventually_cofinite.1 w.2
  set T := hfin.toFinset with hT
  have hPT : P ∉ T := by
    rw [hT, Set.Finite.mem_toFinset]
    exact fun h' => h' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h)
  let e : HeightOneSpectrum (𝓞 E) → ℕ := fun Q => (WithZero.log (Valued.v (w Q))).toNat
  have hbound : ∀ Q ∈ T, ∀ s : 𝓞 E, s ∈ Q.asIdeal ^ e Q →
      Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) * Valued.v (w Q) ≤ 1 := by
    intro Q hQ s hs
    have hQ' : w Q ∉ Q.adicCompletionIntegers E := by rwa [hT, Set.Finite.mem_toFinset] at hQ
    have hne : Valued.v (w Q) ≠ 0 := by
      intro h0
      apply hQ'
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, h0]
      exact zero_le'
    have h1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ WithZero.exp (-((e Q : ℕ) : ℤ)) := by
      show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 hs
    have h2 : Valued.v (w Q) ≤ WithZero.exp ((e Q : ℕ) : ℤ) := by
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      exact Int.self_le_toNat _
    calc _ ≤ WithZero.exp (-((e Q : ℕ) : ℤ)) * WithZero.exp ((e Q : ℕ) : ℤ) := mul_le_mul' h1 h2
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  obtain ⟨s, hs⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert P T)
    (fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) (fun Q => if Q = P then 1 else e Q)
    (fun Q _ => Q.prime) (fun Q _ Q' _ hne h' => hne (HeightOneSpectrum.ext h'))
    (fun Q => if Q.1 = P then 1 else 0)
  have hsP : s ∉ P.asIdeal := by
    intro hm
    have h1 := hs P (Finset.mem_insert_self _ _)
    simp only [if_true, pow_one] at h1
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := P.asIdeal.sub_mem hm h1
    simpa using this
  have hsQ : ∀ Q ∈ T, s ∈ Q.asIdeal ^ e Q := by
    intro Q hQ
    have hQP : Q ≠ P := fun h' => hPT (h' ▸ hQ)
    have h1 := hs Q (Finset.mem_insert_of_mem hQ)
    simpa [hQP] using h1
  refine ⟨s, hsP, ?_⟩
  have hmem : iA F E (algebraMap (𝓞 E) E s) * z ∈ RInt F E := by
    refine (hι.2 _).2 fun Q => ?_
    have e1 : ι (iA F E (algebraMap (𝓞 E) E s) * z) Q =
        algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * w Q := by
      rw [map_mul, show ι (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) from hι.1 _]
      rfl
    rw [e1, map_mul]
    by_cases hQ : Q ∈ T
    · exact hbound Q hQ s (hsQ Q hQ)
    · have hQ' : w Q ∈ Q.adicCompletionIntegers E := by
        by_contra hc
        exact hQ (by rw [hT, Set.Finite.mem_toFinset]; exact hc)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hQ'
      have hs1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ 1 := by
        show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_le_one _ _
      exact mul_le_one' hs1 hQ'
  exact hmem

def compAt (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) : AfE F E →+* P.adicCompletion E where
  toFun a := ι a P
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add (f := _)]; rfl

theorem exists_nearAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N n : ℕ)
    (P : HeightOneSpectrum (𝓞 E)) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : ∃ g : GL (Fin N) E, NearAt P n y g := by
  classical
  obtain ⟨ι, hι⟩ := exists_isAdIso F E
  set Φ := compAt ι P with hΦ
  have hΦi : ∀ x : E, Φ (iA F E x) = algebraMap E (P.adicCompletion E) x := by
    intro x
    show (ι (iA F E x)) P = _
    rw [show ι (iA F E x) = algebraMap E _ x from hι.1 x]
    rfl
  set A : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hA
  set B : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  set qq : P.adicCompletion E := algebraMap E _ ((((qOf P : ℕ) : E) ^ n)⁻¹) with hqq
  let S : Set (Matrix (Fin N) (Fin N) (P.adicCompletion E)) :=
    {G | G.det ≠ 0} ∩ ⋂ a : Fin N, ⋂ b : Fin N, {G | Valued.v (qq * (A * G - 1) a b) ≤ 1}
  have hSo : IsOpen S := by
    refine IsOpen.inter (isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const) ?_
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    have hc : Continuous fun G : Matrix (Fin N) (Fin N) (P.adicCompletion E) => qq * (A * G - 1) a b := by
      refine continuous_const.mul ?_
      exact ((continuous_const.matrix_mul continuous_id).sub continuous_const).matrix_elem a b
    exact (Valued.isOpen_integer (P.adicCompletion E)).preimage hc
  have hBS : B ∈ S := by
    refine ⟨?_, Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => ?_⟩
    · intro h0
      have := congrArg Matrix.det hAB
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    · show Valued.v (qq * (A * B - 1) a b) ≤ 1
      rw [hAB, sub_self]
      simp
  have hd : DenseRange fun g : Matrix (Fin N) (Fin N) E => g.map (algebraMap E (P.adicCompletion E)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => HeightOneSpectrum.denseRange_algebraMap E P
  obtain ⟨g0, hg0⟩ := hd.exists_mem_open hSo ⟨B, hBS⟩
  obtain ⟨hdet, hcong⟩ := hg0
  have hdet0 : g0.det ≠ 0 := by
    intro h0
    apply hdet
    show (g0.map (algebraMap E (P.adicCompletion E))).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0, fun a b => ?_⟩
  refine intAtA_of_val hι P _ ?_
  have hc : Valued.v (qq * (A * g0.map (algebraMap E (P.adicCompletion E)) - 1) a b) ≤ 1 :=
    Set.mem_iInter.1 (Set.mem_iInter.1 hcong a) b
  refine Eq.trans_le ?_ hc
  congr 1
  show Φ _ = _
  rw [map_mul, hΦi]
  congr 1
  have e1 : ((y⁻¹ * ratA F (Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 =
      ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) * g0.map (iA F E) - 1 := rfl
  rw [e1]
  have e2 : Φ (((((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1 :
      Matrix (Fin N) (Fin N) (AfE F E))) a b) =
      Φ.mapMatrix (((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1) a b := rfl
  have e3 : Φ.mapMatrix (g0.map (iA F E)) = g0.map (algebraMap E (P.adicCompletion E)) :=
    Matrix.ext fun i j => hΦi (g0 i j)
  rw [e2, map_sub, map_mul, map_one, e3]

end GlobalTheory.TwU.Approx
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeamGLInjective

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

section Seam

variable {D : D7} {X : Fields} (s : Seam D X)

def seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv X.E (Fin n → X.E)
    (Matrix.GeneralLinearGroup.toLin (bc (s.iE.symm : D.host.E →+* X.E) g))

theorem seamGL_seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : seamGL s (seamLE s g) = g := by
  ext a b
  simp [seamGL, seamLE, bc]

end Seam

end GlobalTheory.TwU

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveIntegralRightTranslate

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open GlobalTheory.TopStep
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameShift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_glint_nearAt {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : ℕ)
    (k : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hk : CongAt (seamP s P) 0 k) (hk' : CongAt (seamP s P) 0 k⁻¹) :
    ∃ g : GLint X.E n P, NearAt (seamP s P) d k (seamGL s g.1) := by
  obtain ⟨g0, hg0⟩ := GlobalTheory.TwU.Approx.exists_nearAt D.host.F D.host.E n (d + 1) (seamP s P) k
  set h := seamLE s g0 with hhdef
  have hh : seamGL s h = g0 := seamGL_seamLE s g0
  have hC : CongAt (F := D.host.F) (seamP s P) (d + 1) (k⁻¹ * ratA D.host.F (seamGL s h)) := by
    rw [hh]; exact hg0
  have h0 : CongAt (F := D.host.F) (seamP s P) 0 (ratA D.host.F (seamGL s h)) := by
    have e : ratA D.host.F (seamGL s h) = k * (k⁻¹ * ratA D.host.F (seamGL s h)) := by group
    rw [e]
    exact GlobalTheory.CplPt.congAt_mul 0 hk (GlobalTheory.FrameMove.congAt_mono (Nat.zero_le _) hC)
  have h0' : CongAt (F := D.host.F) (seamP s P) 0 (ratA D.host.F (seamGL s h⁻¹)) := by
    rw [map_inv, map_inv]
    have e : (ratA D.host.F (seamGL s h))⁻¹ = (k⁻¹ * ratA D.host.F (seamGL s h))⁻¹ * k⁻¹ := by group
    rw [e]
    exact GlobalTheory.CplPt.congAt_mul 0 (GlobalTheory.FrameMove.congAt_mono (Nat.zero_le _)
      (GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ (Nat.succ_pos d) hC)) hk'
  have l1 := GlobalTheory.TwU.MidIndep.congAt_local s P 0 n h h0
  have l2 := GlobalTheory.TwU.MidIndep.congAt_local s P 0 n h⁻¹ h0'
  have hmem : h ∈ GLint X.E n P := by
    refine fun w => ⟨fun hw => ?_, fun hw => GlobalTheory.FrameMove.mem_of_local P 0 h l1 w hw⟩
    have := GlobalTheory.FrameMove.mem_of_local P 0 h⁻¹ l2 _ hw
    rwa [show (h⁻¹ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (h w) = w from h.symm_apply_apply w] at this
  refine ⟨⟨h, hmem⟩, ?_⟩
  show CongAt _ d (k⁻¹ * ratA D.host.F (seamGL s h))
  exact GlobalTheory.FrameMove.congAt_mono (Nat.le_succ d) hC

end GlobalTheory.FrameShift

namespace GlobalTheory.FrameShift

theorem exists_pt_mul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (y k : SB t μ → GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 (k P) ∧ CongAt (seamP t.seam P.1) 0 (k P)⁻¹) → (∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P) (seamGL t.seam (frsF t.sel (t.tup μ) p P))) → ∃ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i, p'.deco.1.N = p.deco.1.N ∧ p'.deco.1.f = p.deco.1.f ∧ ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P * k P) (seamGL t.seam (frsF t.sel (t.tup μ) p' P))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i p y k hk hy
  choose g hg using fun P : SB t μ => exists_glint_nearAt t.seam P.1 ((t.cst μ).D P) (k P) (hk P).1 (hk P).2
  obtain ⟨q, κ, hN, hf, hfr, hκ⟩ := GlobalTheory.CplPt.exists_pt_frames p g
  refine ⟨q, hN, hf, fun P => ?_⟩
  have base := GlobalTheory.CplPt.nearAt_mul_int _ (hy P) (hg P) (GlobalTheory.CplPt.seamGL_int t.seam (g P))
  rw [hfr P, map_mul]
  by_cases hP : P.1 ∈ t.Pr.vGs
  · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
    have hq := (GlobalTheory.ColPeriod.levelPrimes t.X t.Pr t.sel t.S (t.tup μ) hPin.fields.ok t.pr_ok hPin.sel P).1.2
    have e : ((κ P)⁻¹).1 = (g P).1 * ((g P)⁻¹ * (κ P)⁻¹).1 := by
      rw [← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [e, map_mul, ← mul_assoc]
    refine GlobalTheory.CplPt.nearAt_mul _ base ?_
    rw [hD]
    exact GlobalTheory.CplPt.congAt_one_of_redGL t.seam hq ((g P)⁻¹ * (κ P)⁻¹) (hκ P).1
  · rw [(hκ P).2 hP]
    exact base

end GlobalTheory.FrameShift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveIntegralRightTranslateStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.chartPoint_frames_move_integralRightTranslate : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (y k : SB t μ → GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 (k P) ∧ CongAt (seamP t.seam P.1) 0 (k P)⁻¹) → (∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P) (seamGL t.seam (frsF t.sel (t.tup μ) p P))) → ∃ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i, p'.deco.1.N = p.deco.1.N ∧ p'.deco.1.f = p.deco.1.f ∧ ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P * k P) (seamGL t.seam (frsF t.sel (t.tup μ) p' P))) := by
  first | exact @GlobalTheory.FrameShift.exists_pt_mul | exact GlobalTheory.FrameShift.exists_pt_mul | (intros; apply GlobalTheory.FrameShift.exists_pt_mul <;> assumption)
end
end

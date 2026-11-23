module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNorm
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
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCong
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Formalism.LocalToGlobal.Columns.QthExistsBound
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSubgroupMemLevelTwistPrimeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNormStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ) (P : SB), 1 ≤ dep P →
    ∀ (κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (g C : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)), InFrame s fb dep P κ g →
    CongAt (F := D.host.F) (seamP s P.1) (dep P) (ratA D.host.F (seamGL s C)) →
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det (g * C) : X.Eˣ) : X.E)) - 1)) := by
  first | exact @GlobalTheory.FramesDet.det_frame_mul_congAt | exact GlobalTheory.FramesDet.det_frame_mul_congAt | (intros; apply GlobalTheory.FramesDet.det_frame_mul_congAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramesOfRightTranslatePointPrincipalCongruence

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.LevFrames

open Matrix

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem intAtA_neg' (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) :
    IntAtA (F := F) P (-a) := by
  have := GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int (F := F) (P := P) (-1)) h
  simpa using this

theorem intAtA_pow' (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) (m : ℕ) :
    IntAtA (F := F) P (a ^ m) := by
  induction m with
  | zero => simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 1
  | succ m ih => rw [pow_succ]; exact GlobalTheory.CplPt.intAtA_mul ih h

theorem core [StarRing E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (G G₁ : GL (Fin N) E)
    (h : CongAt Q n (y⁻¹ * ratA F G)) (h₁ : CongAt Q n (y⁻¹ * ratA F G₁)) (a b : Fin N) :
    IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * (((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set qi := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hqi
  set d := iA F E (((qOf Q : ℕ) : E) ^ n) with hdd
  have hdq : d * qi = 1 := by
    rw [hqi, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have hd : IntAtA (F := F) Q d := by
    have := GlobalTheory.CplPt.intAtA_int (F := F) (P := Q) (((qOf Q : ℕ) : 𝓞 E) ^ n)
    simpa [hdd] using this
  set Am : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hAm
  set Bm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hBm
  set Mm : Matrix (Fin N) (Fin N) E := ((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1 with hMm
  set Mh : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Mm.map (iA F E) with hMh
  have hMh' : Mh = ((ratA F (G⁻¹ * G₁) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 := by
    rw [hMh, hMm, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have key : (1 + Am) * (1 + Mh) = 1 + Bm := by
    rw [hMh', hAm, hBm, add_sub_cancel, add_sub_cancel, add_sub_cancel, ← Units.val_mul]
    congr 1
    rw [map_mul, map_inv]
    group
  have e1 : Mh = Bm - Am - Am * Mh := by
    have e0 : Mh = (1 + Am) * (1 + Mh) - 1 - Am - Am * Mh := by noncomm_ring
    rw [key] at e0
    exact e0.trans (by noncomm_ring)
  have hA : ∀ i j, IntAtA (F := F) Q (qi * Am i j) := fun i j => h i j
  have hB : ∀ i j, IntAtA (F := F) Q (qi * Bm i j) := fun i j => h₁ i j
  have step : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ (m + 1) * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j)) := by
    intro m hm i j
    have e2 : d ^ m * (qi * Mh i j) = d ^ m * (qi * Bm i j) + -(d ^ m * (qi * Am i j)) +
        -(∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j))) := by
      have es : ∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)) = d ^ m * (qi * ∑ l, Am i l * Mh l j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (d ^ m * qi * Am i l * Mh l j) * hdq
      rw [es]
      conv_lhs => rw [e1]
      simp only [Matrix.sub_apply, Matrix.mul_apply (M := Am)]
      ring
    rw [e2]
    exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hB i j))
      (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hA i j))))
      (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_sum _ _ fun l _ => GlobalTheory.CplPt.intAtA_mul (hA i l) (hm l j)))
  have desc : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (qi * Mh i j) := by
    intro m
    induction m with
    | zero => intro hm i j; simpa using hm i j
    | succ m ih => intro hm; exact ih (step m hm)
  obtain ⟨J, hJ⟩ := qth_bound Q Mm
  have hqv : Q.valuation E ((qOf Q : ℕ) : E) ≤ WithZero.exp (-1 : ℤ) := by
    have h0 : ((qOf Q : ℕ) : 𝓞 E) ∈ Q.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem _
    have := (Q.intValuation_le_pow_iff_mem _ 1).2 h0
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)] at this
    simpa using this
  have hbig : ∀ i j, IntAtA (F := F) Q (d ^ (J + 1) * (qi * Mh i j)) := by
    intro i j
    have e : d ^ (J + 1) * (qi * Mh i j) = iA F E (((qOf Q : ℕ) : E) ^ (n * J) * Mm i j) := by
      rw [hMh, Matrix.map_apply, hdd, hqi, ← map_pow, ← map_mul, ← map_mul]
      congr 1
      rw [pow_succ, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq), ← pow_mul]
    rw [e]
    refine GlobalTheory.CplPt.intAtA_of_intAt ((qth_intAt_iff Q _).2 ?_)
    rw [map_mul, map_pow]
    calc Q.valuation E ((qOf Q : ℕ) : E) ^ (n * J) * Q.valuation E (Mm i j) ≤ WithZero.exp (-1 : ℤ) ^ (n * J) * WithZero.exp (J : ℤ) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le hqv _) (hJ i j)
      _ ≤ 1 := by
          rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
          have : (J : ℤ) ≤ (n : ℤ) * J := by exact_mod_cast Nat.le_mul_of_pos_left J hn
          rw [nsmul_eq_mul]
          push_cast
          linarith
  have hfin := desc (J + 1) hbig a b
  show IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b)
  refine GlobalTheory.RatInt.intAt_of_intAtA (F := F) Q _ ?_
  have e3 : iA F E ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b) = qi * Mh a b := by rw [map_mul, hMh, Matrix.map_apply]
  rw [e3]
  exact hfin

end Core

section Seam

open Formalism.L2.Ker Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X)

theorem intAt_of_seamP (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E) (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  set f := RingOfIntegers.mapRingEquiv s.iE
  refine ⟨f.symm r, f.symm c, fun hm => hc ?_, ?_⟩
  · have := (mem_seamP s P (f.symm c)).2 hm
    rwa [show (RingOfIntegers.mapRingEquiv s.iE) (f.symm c) = c from f.apply_symm_apply c] at this
  · apply s.iE.injective
    rw [map_mul]
    have h1 : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E (f.symm w)) = algebraMap (𝓞 D.host.E) D.host.E w := by
      intro w
      have h2 : ∀ x : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E x) = algebraMap (𝓞 D.host.E) D.host.E (f x) := fun x => rfl
      rw [h2, f.apply_symm_apply]
    rw [h1, h1, e]

end Seam

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem frames_lev : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (a : 𝓞 D.host.E) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), x₁.1 = x.1 * κ →
    ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (g : GLint t.X.E (D.R.N j) P.1), InFrame t.seam (A.fb j hj β) (t.cst μ).D P κ g.1 →
    ∃ C : GLint t.X.E (D.R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (D.R.N j) P.1 ((t.cst μ).D P) ∧
      CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (seamGL t.seam C.1)) ∧
      frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * (g * C).1 := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A a j hj β x x₁ κ hx p p₁ hp hp₁ P g hg
  have hD : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  set F₀ := frsF t.sel (t.tup μ) p P with hF₀
  set F₁ := frsF t.sel (t.tup μ) p₁ P with hF₁
  have hX : NearAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) *
        ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P)))
      (seamGL t.seam F₀ * seamGL t.seam g.1) :=
    GlobalTheory.CplPt.nearAt_mul_int _ (hp.frame P) hg (GlobalTheory.CplPt.seamGL_int t.seam g)
  have e : ratA D.host.F (A.crd j hj) * x₁.1 * ratA D.host.F (A.fb j hj β P) =
      (ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) *
        ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P)) := by
    rw [hx]; group
  have hX₁ := hp₁.frame P
  rw [e, ← hF₁] at hX₁
  have hc := core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD _ _ _ hX hX₁
  set C₀ := g.1⁻¹ * F₀⁻¹ * F₁ with hC₀
  have hM : (seamGL t.seam F₀ * seamGL t.seam g.1)⁻¹ * seamGL t.seam F₁ = seamGL t.seam C₀ := by
    rw [hC₀, map_mul, map_mul, map_inv, map_inv, _root_.mul_inv_rev]
  simp only [hM] at hc
  have hcol : ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ *
      (C₀ (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N j)) l)) := by
    intro s l
    have hc' := hc l s
    rw [GlobalTheory.TwU.MidIndep.qOf_seamP] at hc'
    refine intAt_of_seamP t.seam P.1 _ ?_
    convert hc' using 1
    have hm := congrFun (seamGL_mulVec t.seam C₀ (Pi.single s 1)) l
    have hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N _)) j)) = Pi.single s (1 : D.host.E) := by
      funext j
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [hs1, Matrix.mulVec_single_one] at hm
    rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
    by_cases h : l = s
    · subst h; simp [Matrix.col_apply]
    · simp [h, Matrix.col_apply]
  obtain ⟨hk, hpc⟩ := GlobalTheory.CongOne.mem_glint_prinCong_of_cols P.1 ((t.cst μ).D P) C₀ hD hcol
  refine ⟨⟨C₀, hk⟩, hpc, fun a' b' => ?_, ?_⟩
  · have h1 := GlobalTheory.CplPt.intAtA_of_intAt (F := D.host.F) (hc a' b')
    convert h1 using 2
    rw [map_mul (iA D.host.F D.host.E), Matrix.sub_apply, Matrix.sub_apply, map_sub (iA D.host.F D.host.E), GlobalTheory.CplPt.ratA_apply,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · show F₁ = F₀ * (g.1 * C₀)
    rw [hC₀]
    group

end GlobalTheory.LevFrames
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramesOfRightTranslatePointPrincipalCongruenceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.frames_of_right_translate_point_principal_congruence : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (a : 𝓞 D.host.E) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), x₁.1 = x.1 * κ →
    ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (g : GLint t.X.E (D.R.N j) P.1), InFrame t.seam (A.fb j hj β) (t.cst μ).D P κ g.1 →
    ∃ C : GLint t.X.E (D.R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (D.R.N j) P.1 ((t.cst μ).D P) ∧
      CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (seamGL t.seam C.1)) ∧
      frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * (g * C).1 := by
  first | exact @GlobalTheory.LevFrames.frames_lev | exact GlobalTheory.LevFrames.frames_lev | (intros; apply GlobalTheory.LevFrames.frames_lev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelMovedPointFramesMatrixSteps

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.MatFrames



theorem frames_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j < D.R.m), j ≤ t.m2 → ∀ (β : (St j hj.le).Ch) (x x₁ : UA D j hj.le) (κ : ((St j hj.le).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj.le β x p → IsPtAd A a j hj.le β x₁ p₁ →
    ∃ (k : GLQ t.X.E (D.R.N j) (SB t μ)) (c : SB t μ → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * ((k P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P (k P) (c P)) ∧
      ((((St j hj.le).K β).lev.chi κ : ℂˣ) : ℂ) = t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) ∧
      ∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE ((LinearEquiv.det ((k P)⁻¹).1 : t.X.Eˣ) : t.X.E)) - 1))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie j hj hjm β x x₁ κ hx p p₁ hp hp₁
  classical
  have hok := t.idx_ok μ
  obtain ⟨hLe, -, hChi⟩ := hTie.levMid j hj hjm β
  have hLoc : ∀ P : SB t μ, ∃ g z, A.midRel j hj β P g z ∧ InFrame t.seam (A.fb j hj.le β) (t.cst μ).D P κ.1 g := by
    intro P
    have hv : IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    have hU := (((St j hj.le).K β).lev.U_eq κ.1).1 κ.2
    exact hLe P _ hv κ.1 hU.1 (hU.2 _)
  choose g z hgz using hLoc
  have hpr : ∀ P, g P ∈ prCat (Pr := t.Pr) (t.cst μ).sharp j P.1 ((t.idx μ).h j (A.ib j hj β) P) := fun P =>
    (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) j P _ (g P)).1 ⟨z P, (hgz P).1⟩
  let gg : ∀ P : SB t μ, GLint t.X.E (D.R.N j) P.1 := fun P => ⟨g P, hok.int j _ P (hpr P)⟩
  have hB := fun P => GlobalTheory.T.frames_of_right_translate_point_principal_congruence A a j hj.le β x x₁ κ.1 hx p p₁ hp hp₁ P (gg P) (hgz P).2
  choose C hCp hCc hCf using hB
  have hD : ∀ P : SB t μ, 1 ≤ (t.cst μ).D P := fun P => hok.cst_ok.D_pos P
  have hc : ∀ P : SB t μ, ∃ c : t.X.Kˣ, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P
      (gg P * C P)⁻¹ c ∧ (c : t.X.K) = (z P)⁻¹ := by
    intro P
    obtain ⟨r, hr, hrx, hz⟩ := (hgz P).1
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hH : redGL _ P.1 (gg P) ∈ ((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).H :=
        (hok.grpG j _ ⟨P.1, hP⟩ _).2 ⟨g P, hpr P, fun y hy => redV_redGL (gg P) hy⟩
      have hlam := hok.chrG j _ ⟨P.1, hP⟩ ⟨_, hH⟩ (g P) r hr hrx (fun y hy => redV_redGL (gg P) hy)
      have hred : redGL _ P.1 (gg P * C P)⁻¹ = (redGL _ P.1 (gg P))⁻¹ := by
        rw [map_inv, map_mul, GlobalTheory.TopStep.redGL_of_prinCong (hD P) (hCp P), mul_one]
      refine ⟨(((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).lam ⟨_, hH⟩)⁻¹, ⟨fun hP' => ⟨hred ▸ inv_mem hH, ?_⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
      · rw [← map_inv]
        congr 1
        exact Subtype.ext hred.symm
      · rw [Units.val_inv_eq_inv_val, hlam, hz]
    · have hQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.mp P.2).resolve_left hP
      obtain ⟨r', hr', hr'x, hr'1⟩ := GlobalTheory.T.principal_congruence_subgroup_mem_level_twist_prime hPin.fields.ok t.pr_ok hok (j := j) hjm (A.ib j hj β) P hP (C P) (hCp P)
      have hgH : gg P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 (hpr P)
      have hCH : C P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 ⟨r', hr', hr'x⟩
      have hlg := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨gg P, hgH⟩ r hr hrx
      have hlC := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨C P, hCH⟩ r' hr' hr'x
      have hC1 : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨C P, hCH⟩ = 1 := Units.ext (hlC.trans hr'1)
      refine ⟨(((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨gg P, hgH⟩)⁻¹,
        ⟨fun hP' => absurd hP' hP, fun hQ' _ => ⟨inv_mem (mul_mem hgH hCH), ?_⟩⟩, ?_⟩
      · have e : (⟨(gg P * C P)⁻¹, inv_mem (mul_mem hgH hCH)⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) =
            ((⟨gg P, hgH⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) * ⟨C P, hCH⟩)⁻¹ := Subtype.ext (by simp)
        rw [e, map_inv, map_mul, hC1, mul_one]
      · rw [Units.val_inv_eq_inv_val, hlg, hz]
  choose c hcL hcz using hc
  refine ⟨fun P => (gg P * C P)⁻¹, c, fun P => ?_, hcL, ?_, fun P => ?_⟩
  · rw [inv_inv]
    exact hCf P
  · have h1 := hChi κ g z hgz
    have h2 : (((∏ P, c P : t.X.Kˣ)) : t.X.K) = (∏ P, z P)⁻¹ := by
      rw [Units.coe_prod, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun P _ => hcz P
    rw [h2, map_inv₀]
    exact eq_inv_of_mul_eq_one_left h1
  · rw [inv_inv]
    exact GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm t.seam (A.fb j hj.le β) (t.cst μ).D P (hD P) κ.1 (g P) (C P).1 (hgz P).2 (hCc P)

end GlobalTheory.MatFrames

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelMovedPointFramesMatrixStepsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.levelMoved_point_frames_matrixSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j < D.R.m), j ≤ t.m2 → ∀ (β : (St j hj.le).Ch) (x x₁ : UA D j hj.le) (κ : ((St j hj.le).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj.le β x p → IsPtAd A a j hj.le β x₁ p₁ →
    ∃ (k : GLQ t.X.E (D.R.N j) (SB t μ)) (c : SB t μ → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * ((k P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P (k P) (c P)) ∧
      ((((St j hj.le).K β).lev.chi κ : ℂˣ) : ℂ) = t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) ∧
      ∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE ((LinearEquiv.det ((k P)⁻¹).1 : t.X.Eˣ) : t.X.E)) - 1))) := by
  first | exact @GlobalTheory.MatFrames.frames_mat | exact GlobalTheory.MatFrames.frames_mat | (intros; apply GlobalTheory.MatFrames.frames_mat <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelAtBadPrimes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelKeepsBaseCosetStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStepStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chartPoint_right_translate_by_level_coupled_step : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hj : t.m2 + 1 ≤ D.R.m) (β' : (St (t.m2 + 1) hj).Ch)
    (x' x₁' : UA D (t.m2 + 1) hj) (κ' : ((St (t.m2 + 1) hj).K β').lev.U) p', x₁'.1 = x'.1 * κ'.1 → IsPtAd A a (t.m2 + 1) hj β' x' p' →
    ∃ (q' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
      IsPtAd A a (t.m2 + 1) hj β' x₁' q' ∧
      (∀ (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) w, phiT t.X.K p.deco.1 q'.deco.1 w = phiT t.X.K p.deco.1 p'.deco.1 w) ∧
      (∀ P, frsF t.sel (t.tup μ) q' P = frsF t.sel (t.tup μ) p' P * ((κ'' P)⁻¹).1) ∧
      ∀ P, InFrame t.seam (A.fb (t.m2 + 1) hj β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) := by
  first | exact @GlobalTheory.CplPt.ptAd_levCpl | exact GlobalTheory.CplPt.ptAd_levCpl | (intros; apply GlobalTheory.CplPt.ptAd_levCpl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelAtBadPrimesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.coupledStep_chart_level_at_bad_primes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∃ c : SB t μ → t.X.Kˣ,
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β'))
        ((t.idx μ).levQ (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β')) P (κ'' P) (c P)) ∧
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = ((((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.chi κ' : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CplLev.levAt_cpl | exact GlobalTheory.CplLev.levAt_cpl | (intros; apply GlobalTheory.CplLev.levAt_cpl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetCoupledEqProdLocal

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplMuDet

open Matrix
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

def intAtSub (P : HeightOneSpectrum (𝓞 E)) :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | IntAtA (F := F) P a}
  mul_mem' := GlobalTheory.CplMuDet.intAtA_mul
  one_mem' := by simpa using GlobalTheory.CplMuDet.intAtA_int (F := F) (P := P) 1
  add_mem' := GlobalTheory.CplMuDet.intAtA_add
  zero_mem' := by simpa using GlobalTheory.CplMuDet.intAtA_int (F := F) (P := P) 0
  neg_mem' := by
    intro a ha
    have := GlobalTheory.CplMuDet.intAtA_mul (GlobalTheory.CplMuDet.intAtA_int (F := F) (P := P) (-1)) ha
    simpa using this

theorem det_congAt {d : ℕ} (hd : 1 ≤ d) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P d k) :
    IntAtA (F := F) P (iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1)) := by
  classical
  set S := intAtSub (F := F) P with hS
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set Q := iA F E ((qOf P : ℕ) : E) with hQ
  have hcQ : iA F E ((qOf P : ℕ) : E)⁻¹ * Q = 1 := by rw [hQ, ← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQS : Q ∈ S := by
    have := GlobalTheory.CplMuDet.intAtA_int (F := F) (P := P) ((qOf P : ℕ) : 𝓞 E)
    simpa [hQ] using this
  have hZ : ∀ a b, Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) ∈ S :=
    fun a b => S.mul_mem (S.pow_mem hQS _) (h a b)
  have hZe : ∀ a b, Q * (Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)) =
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b := by
    intro a b
    have e : Q * Q ^ (d - 1) * iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hQ, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
    rw [← mul_assoc, ← mul_assoc, e, one_mul]
  let Z : Matrix (Fin N) (Fin N) S := fun a b => ⟨_, hZ a b⟩
  let q' : S := ⟨Q, hQS⟩
  let M : Matrix (Fin N) (Fin N) S := 1 + q' • Z
  have hM : M.map S.subtype = (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    ext a b
    have e1 : S.subtype ((1 : Matrix (Fin N) (Fin N) S) a b) = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), e1, Matrix.smul_apply, smul_eq_mul, map_mul]
    show _ + Q * (Q ^ (d - 1) * _) = _
    rw [hZe, Matrix.sub_apply]
    ring_nf
  set I : Ideal S := Ideal.span {q'}
  have hMI : M.map (Ideal.Quotient.mk I) = 1 := by
    ext a b
    have hq0 : Ideal.Quotient.mk I q' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), Matrix.smul_apply, smul_eq_mul, map_mul, hq0, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, map_one]
    show (M.map (Ideal.Quotient.mk I)).det = 1
    rw [hMI, Matrix.det_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hdet)
  have hk : ((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      S.subtype M.det := by
    rw [RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Matrix.det hM.symm
  have e2 : iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1) = (w : _) := by
    rw [hk, show S.subtype M.det - 1 = S.subtype (M.det - 1) by simp, ← hw, map_mul]
    show iA F E ((qOf P : ℕ) : E)⁻¹ * ((w : _) * Q) = _
    rw [mul_comm (w : E ⊗[F] FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcQ, one_mul]
  rw [e2]
  exact w.2

end Cong

end GlobalTheory.CplMuDet

namespace GlobalTheory.CplMuDet

open Matrix
open scoped TensorProduct

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ratA (g : GL (Fin n) E) :
    ((Matrix.GeneralLinearGroup.det (ratA F g) : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      iA F E ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Rat

section Frame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X)

theorem det_seamGL {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    ((Matrix.GeneralLinearGroup.det (seamGL s g) : D.host.Eˣ) : D.host.E) = s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) := by
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix',
    LinearEquiv.coe_det]
  rfl

variable {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)

theorem det_inFrame {P : SB} {κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)} (hd : 1 ≤ dep P) (h : InFrame s fb dep P κ g) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) - 1)) := by
  have H := det_congAt hd h
  have e : ((Matrix.GeneralLinearGroup.det (((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P))⁻¹ *
      ratA D.host.F (seamGL s g)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) =
      (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Units.val_mul, det_ratA, det_seamGL]
    congr 2
    rw [mul_comm, mul_inv_cancel_left]
  rw [← e]
  exact H

end Frame

end GlobalTheory.CplMuDet

theorem GlobalTheory.CplMuDet.muOf_det_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU → ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ'.1) =
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ'' P).1 : t.X.Eˣ) : t.X.E))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hMu β' κ' κ'' hF
  have hlt : t.m2 < D.R.m := by have := cpl_lt t μ; omega
  obtain ⟨-, h⟩ := GlobalTheory.LevMuDet.muOf_det_lev A dtU a hPin hTie hMu t.m2 hlt (t.m2 + 1) (cpl_lt t μ).le β' κ'
    (fun P => ((LinearEquiv.det ((κ'' P)⁻¹).1 : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.CplMuDet.det_inFrame t.seam _ _ ((t.idx_ok μ).cst_ok.D_pos P) (hF P))
  rw [h]
  congr 1
  exact Finset.prod_congr rfl fun P _ => GlobalTheory.TopLaw.rhoT_inv _ P (κ'' P)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetCoupledEqProdLocalStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.stepCharacter_det_coupled_eq_prod_local : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU → ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ'.1) =
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ'' P).1 : t.X.Eˣ) : t.X.E))) := by
  first | exact @GlobalTheory.CplMuDet.muOf_det_cpl | exact GlobalTheory.CplMuDet.muOf_det_cpl | (intros; apply GlobalTheory.CplMuDet.muOf_det_cpl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumLawTargetLevel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplTarget

section Local

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem xiCpl1_moved (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {u : Pr.Word} {al : L.β m2} {b : L.β (m2 + 1)}
    (p : ChPt (R := R) sel mu u m2) (p' q' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (κ : GLQ X.E (R.N (m2 + 1)) (rowSG Pr sel mu)) (c : rowSG Pr sel mu → X.Kˣ)
    (hfr : ∀ P, frsF sel mu q' P = frsF sel mu p' P * ((κ P)⁻¹).1)
    (hc : ∀ P, GlobalTheory.TopLaw.LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P (κ P) (c P)) (x : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hphi : phiT X.K p.deco.1 q'.deco.1 x = phiT X.K p.deco.1 p'.deco.1 x) :
    XiCpl1 Ch sel mu cst L m2 al p q' Y x * ∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P ((LinearEquiv.det (κ P).1 : X.Eˣ) : X.E) =
      ((∏ P, c P : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  unfold XiCpl1
  rw [hphi, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_mul_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu p P) (frsF sel mu q' P) x = (κ P).1.toLinearMap ∘ₗ inFr (frsF sel mu p P) (frsF sel mu p' P) x := by
    rw [hfr]
    refine LinearMap.ext fun w => ?_
    rfl
  have e2 : (frsF sel mu q' P).symm (repY Y) = (κ P).1 ((frsF sel mu p' P).symm (repY Y)) := by
    rw [hfr]
    rfl
  rw [e1, e2]
  exact GlobalTheory.CoupledLaw.psiAt_target hX hPr hL (hc P) (L.h m2 al P) _ _

end Local



theorem levAt_target : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi) (κ' : ((St (i + 1) hi).K β').lev.U) p p' p₁',
    x₁'.1 = x'.1 * κ'.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a (i + 1) hi β' x₁' p₁' → ∀ w,
    muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * t.seam.σ₀ (xiPt A i hi β β' p p₁' w) =
      ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT' _hE hMu i hi hi2 hAw β β' x x' x₁' κ' p p' p₁' hx hp hp' hp₁' w
  subst hi2
  obtain ⟨q', κ'', hq', hphi, hfr, hin⟩ := GlobalTheory.T.chartPoint_right_translate_by_level_coupled_step A dtU a hP hT' hi β' x' x₁' κ' p' hx hp'
  obtain ⟨c, hc, hχ⟩ := GlobalTheory.T.coupledStep_chart_level_at_bad_primes A dtU a hP hT' β' κ' κ'' hin
  have hst := GlobalTheory.T.coupledStepChartLevel_keeps_baseCoset A dtU a hP hT' β' κ' κ'' hin
  have hmu := GlobalTheory.T.stepCharacter_det_coupled_eq_prod_local A dtU a hP hT' hMu β' κ' κ'' hin
  have hAw' := hAw β β' x x₁' x x₁' p q' p p₁' hp hq' hp hp₁' fun v _ => ⟨rfl, rfl⟩
  rw [hAw']
  have law := xiCpl1_moved (Ch := t.Ch) (cst := t.cst μ) hP.fields.ok t.pr_ok (t.idx_ok μ) (al := A.ib t.m2 hi β)
    (b := A.ib (t.m2 + 1) (cpl_lt t μ) β') p p' q' (cosetOf A (t.m2 + 1) hi β' p') κ'' c hfr hc w (hphi p w)
  have hcos : cosetOf A (t.m2 + 1) hi β' q' = cosetOf A (t.m2 + 1) hi β' p' := by
    ext y
    unfold cosetOf y0At
    simp only [Set.mem_setOf_eq, dif_pos rfl]
    refine forall_congr' fun P => ?_
    rw [hfr P]
    exact hst P _
  have ex1 : xiPt A t.m2 hi β β' p q' w = XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hi β) p q'
      (cosetOf A (t.m2 + 1) hi β' q') w := by
    unfold xiPt
    rw [dite_eq_right (lt_irrefl _), if_pos rfl]
  have ex2 : xiPt A t.m2 hi β β' p p' w = XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hi β) p p'
      (cosetOf A (t.m2 + 1) hi β' p') w := by
    unfold xiPt
    rw [dite_eq_right (lt_irrefl _), if_pos rfl]
  rw [ex1, ex2, hcos, hmu, ← hχ, ← map_mul, ← map_mul, mul_comm (∏ P : SB t μ, _), law]

end GlobalTheory.CplTarget
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumLawTargetLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.firstCoupledStep_adelicDatum_law_targetLevel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi) (κ' : ((St (i + 1) hi).K β').lev.U) p p' p₁',
    x₁'.1 = x'.1 * κ'.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a (i + 1) hi β' x₁' p₁' → ∀ w,
    muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * t.seam.σ₀ (xiPt A i hi β β' p p₁' w) =
      ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  first | exact @GlobalTheory.CplTarget.levAt_target | exact GlobalTheory.CplTarget.levAt_target | (intros; apply GlobalTheory.CplTarget.levAt_target <;> assumption)
end
end

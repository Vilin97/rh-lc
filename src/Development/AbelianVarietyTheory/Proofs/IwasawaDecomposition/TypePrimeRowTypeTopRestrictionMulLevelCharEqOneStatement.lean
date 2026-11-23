module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.ChainTopLaw
public import Formalism.LocalToGlobal.Columns.ChainTopLawB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Formalism.LocalToGlobal.Columns.RecLevelDiv
import Formalism.LocalToGlobal.Columns.RecLevelSym
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.LocalToGlobal.Columns.ChainLawTw

section

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TwG

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}


end TwG

section TopG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem clW_lamGBS_lamJsym {K : Type} [Field K] (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {n k₀ r t j rS : ℕ} (hr : r = k₀ + 2 * rS + 1) (ht : 0 < t) (hn : r + j * t ≤ n) (h : r ≤ n) (hkr : k₀ < r)
    (M : ↥(HJsym (𝓞 E ⧸ P.asIdeal) n k₀ r t j rS h)) (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P)
    (hred : ∀ x ∈ stdAt E n P, redV P (κ x) = M.1.1.mulVec (redV P x)) :
    LocE.lamGBS q ψ₀ χ k₀ r t j n 0 κ.toLinearMap = ((lamJsym ψ₀ χ n k₀ r t j rS h M : Kˣ) : K) := by
  subst hr
  apply σ₀.injective
  rw [ctl_lamGBS_lamJ (RingEquiv.refl _) σ₀ ψ₀ χ hkr hn hκ hred, ctl_lamJsym_lamJ σ₀ ψ₀ χ ht hn h M]

end TopG

section TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

end TopLaw

section TwIdx

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m} {m2 : ℕ}

end TwIdx

section TwTop

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m} {m2 : ℕ}
  {Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}

end TwTop

end Formalism.L2.Col
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeRowTypeTopRestrictionMulLevelCharEqOne

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep GlobalTheory.LastSteps

theorem lamGBS_top_mul_lam_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs})
    (h0 : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hh0 : h0 ∈ (rowTyG Ch (rPsymF Ch) w).H)
    (g g' : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    g' ∈ Formalism.L2.Col.GLint X.E (R.N R.m) w.1 →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (g' x) =
      ((diagEmb (𝓞 X.E ⧸ w.1.asIdeal) (Nat.sub_le (R.N R.m) 1) h0)⁻¹ : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x)) →
    CongE w.1 1 g g' →
    LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap *
      (((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) : X.K) = 1 := by
  intro X Pr R Ch w h0 hh0 g g' g'' hJ hcomm hg' hred hcong
  classical
  obtain ⟨σ₀⟩ : Nonempty (X.K →+* ℂ) := inferInstance
  have hN : R.N R.m = (R.N R.m - 1) + 1 := N_m_succ R
  have ht := t_pos R
  have hrr := r_eq_sym R
  have hX' := rank_X'_eq R
  have hint : g'' ∈ GLint X.E (R.N R.m - 1) w.1 := by
    intro x
    have h1 := (Subgroup.mem_inf.1 hJ).1 x
    rwa [lamY_zero] at h1
  have hredr : ∀ x ∈ stdAt X.E (R.N R.m - 1) w.1, redV w.1 (g'' x) = (h0⁻¹).1.mulVec (redV w.1 x) := by
    intro x hx
    let v : Sp X.E (R.N R.m) := fun l => if hl : l.1 < R.N R.m - 1 then x ⟨l.1, hl⟩ else 0
    have hv : v ∈ stdAt X.E (R.N R.m) w.1 := by
      rw [mem_stdAt]
      intro l
      by_cases hl : l.1 < R.N R.m - 1
      · simp only [v, dif_pos hl]
        exact mem_stdAt.1 hx _
      · simp only [v, dif_neg hl]
        exact intAt_zero
    have hpv : prXpG X.E (R.N R.m) v = x := by
      funext i
      have hi : i.1 < R.N R.m - 1 := i.2
      simp [prXpG, LinearMap.funLeft_apply, v, hi]
    have hgx : g'' x = prXpG X.E (R.N R.m) (g v) := by
      have h2 := LinearMap.congr_fun hcomm v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2
      rw [h2, hpv]
    have hc := hcong v hv
    funext i
    have eL : redV w.1 (g'' x) i = redV w.1 (g' v) (Br.iC hN i) := by
      rw [hgx]
      show redP w.1 (g v (Br.iC hN i)) = redP w.1 (g' v (Br.iC hN i))
      have hz := mem_stdAt.1 hc (Br.iC hN i)
      have hq : ((qOf w.1 : ℕ) : X.E) ≠ 0 := qOf_ne_zero
      have e : g v (Br.iC hN i) = g' v (Br.iC hN i) +
          (qOf w.1 : X.E) * (((((qOf w.1 : ℕ) : X.E) ^ 1)⁻¹ • (g v - g' v)) (Br.iC hN i)) := by
        simp only [pow_one, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [mul_inv_cancel_left₀ hq]
        ring
      rw [e, redP_add_q hz]
    rw [eL, hred v hv, ← map_inv, diagEmb_val, (diagMat_mulVec hN _ _).1 i]
    congr 1
    funext j
    show redP w.1 (v (Br.iC hN j)) = redP w.1 (x j)
    have hj : (Br.iC hN j).1 < R.N R.m - 1 := j.2
    simp only [v, dif_pos hj]
    rfl
  have hM : h0⁻¹ ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := inv_mem hh0
  have e1 : psi0P Ch w.1 = Ch.psi0 w := by
    unfold psi0P
    rw [dif_pos w.2]
  have e2 : chiP Ch w.1 = chiAt Ch w := by
    unfold chiP
    rw [dif_pos w.2]
  have hlam : LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap =
      ((lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0⁻¹, hM⟩ : X.Kˣ) : X.K) := by
    rw [e1, e2]
    exact clW_lamGBS_lamJsym σ₀ _ _ hrr ht (by omega) (r_le_X' R) (by omega) ⟨h0⁻¹, hM⟩ g'' hint hredr
  have hr : ((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) =
      lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0, hh0⟩ := rfl
  have hprod : (⟨h0⁻¹, hM⟩ * ⟨h0, hh0⟩ : ↥(HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R))) = 1 :=
    Subtype.ext (inv_mul_cancel h0)
  rw [hlam, hr, ← Units.val_mul, ← map_mul, hprod, map_one, Units.val_one]

end GlobalTheory.Mem.Col2.AdT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeRowTypeTopRestrictionMulLevelCharEqOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.typePrime_rowType_topRestriction_mul_levelChar_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs})
    (h0 : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hh0 : h0 ∈ (rowTyG Ch (rPsymF Ch) w).H)
    (g g' : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    g' ∈ Formalism.L2.Col.GLint X.E (R.N R.m) w.1 →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (g' x) =
      ((diagEmb (𝓞 X.E ⧸ w.1.asIdeal) (Nat.sub_le (R.N R.m) 1) h0)⁻¹ : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x)) →
    CongE w.1 1 g g' →
    LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap *
      (((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) : X.K) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | exact GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | (intros; apply GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one <;> assumption)
end
end

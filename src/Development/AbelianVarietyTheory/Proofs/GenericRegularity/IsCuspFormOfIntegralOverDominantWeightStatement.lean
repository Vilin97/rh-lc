module

public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddOfMemHolSub
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecMulAndConstTermMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalOfLeHolSub
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecPowSuccAndConstTermPowSucc

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem bddSec_pow_succ_and_constTerm_pow_succ
    (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) (m : ℕ) :
    X.IsBddSec ((m + 1) • la) (P ^ (m + 1)) ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom,
      X.fj ((m + 1) • la) ξ 0 (P ^ (m + 1)) x = X.fj la ξ 0 P x ^ (m + 1) := by
  induction m with
  | zero =>
    simp only [zero_add, one_smul, pow_one]
    exact ⟨hP, fun _ _ _ _ => trivial⟩
  | succ m ih =>
    have h := bddSec_mul_and_constTerm_mul E r X ((m + 1) • la) la (P ^ (m + 1)) P ih.1 hP
    rw [succ_nsmul la (m + 1), pow_succ P (m + 1)]
    refine ⟨h.1, fun ξ hξ x hx => ?_⟩
    rw [h.2 ξ hξ x hx, ih.2 ξ hξ x hx, pow_succ _ (m + 1)]

theorem cuspForm_of_bddSec_of_pow_succ :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
      ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (m : ℕ), X.IsBddSec la P →
        P ^ (m + 1) ∈ X.SS ((m + 1) • la) → P ∈ X.SS la := by
  intro E _ _ _ r X la P m hP hpow
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  have h := (bddSec_pow_succ_and_constTerm_pow_succ E r X la P hP m).2 ξ hξ x hx
  rw [hpow.2 ξ hξ x hx] at h
  exact pow_eq_zero_iff (Nat.succ_ne_zero m) |>.1 h.symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvalIsHomogeneousMemCuspForms

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem multiset_prod_mem_cuspForms {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (hw : ∀ i, w i ∈ X.SS la) (s : Multiset (Fin N)) (hs : s ≠ 0) :
    (s.map w).prod ∈ X.SS (s.card • la) := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    by_cases h0 : s = 0
    · subst h0
      simpa using hw a
    · have h := (siegelSpaceAlgebra_holds (E := E) r X (s.card • la) la 0).2.1 _ (ih h0) _ (hw a).1
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, succ_nsmul, mul_comm]
      exact h

theorem eval_isHomogeneous_mem_cuspForms :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
      ∀ (la : Wt X.Ψ r) (N d : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (p : MvPolynomial (Fin N) ℂ),
        (∀ i, w i ∈ X.SS la) → 0 < d → p.IsHomogeneous d →
        (fun x => MvPolynomial.eval (fun i => w i x) p) ∈ X.SS (d • la) := by
  intro E _ _ _ r X la N d w p hw hd hp
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X (d • la) (d • la) 0
  have hmon : ∀ m ∈ p.support, (m.toMultiset.map w).prod ∈ X.SS (d • la) := by
    intro m hm
    have hc : m.toMultiset.card = d := by
      rw [Finsupp.card_toMultiset]
      have := hp (MvPolynomial.mem_support_iff.1 hm)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    have := multiset_prod_mem_cuspForms X la w hw m.toMultiset (by
      intro h; rw [h] at hc; simp at hc; omega)
    rwa [hc] at this
  have heq : (fun x => MvPolynomial.eval (fun i => w i x) p) =
      ∑ m ∈ p.support, p.coeff m • (m.toMultiset.map w).prod := by
    funext x
    rw [MvPolynomial.eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
    simp [Finsupp.prod, Finset.prod_apply]
  rw [heq]
  exact Finset.sum_induction _ (fun P => P ∈ X.SS (d • la)) (fun a b ha hb => hadd a ha b hb) h0
    (fun m hm => hsmul _ _ (hmon m hm))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsBddSecOfIntegral

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem isBddSec_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ (la : Wt X.Ψ r) (N k m : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (cf : ℕ → MvPolynomial (Fin N) ℂ) (g : Frame X.Ψ r → ℂ), (∀ i, X.IsBddSec la (w i)) → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → X.IsSec (k • la) g → (∀ x ∈ X.dom, g x * g x ^ m + ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i = 0) → X.IsBddSec (k • la) g := by
  intro E _ _ _ r X la N k m w cf g hw hcf hg heq
  refine ⟨hg, ?_⟩
  choose B hB using fun i => (hw i).2
  obtain ⟨C, hC0, hC⟩ := IntegralCusp.exists_root_bound N k m cf hcf
  refine ⟨C * (∑ i, |B i|) ^ k, fun x hx => ?_⟩
  have h2 := hC _ _ (heq x hx)
  set ν := X.nfac la x with hν
  have hν0 : 0 ≤ ν := Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _
  have h3 : ‖fun i => w i x‖ * ν ≤ ∑ i, |B i| := by
    rw [mul_comm, ← Real.norm_of_nonneg hν0, ← norm_smul,
      pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    intro i
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hν0, mul_comm]
    exact ((hB i x hx).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  show ‖g x‖ * X.nfac _ x ≤ _
  rw [IntegralCusp.nfac_nsmul X la (k • la) k (fun τ i => by simp), ← hν]
  calc _ ≤ C * ‖fun i => w i x‖ ^ k * ν ^ k :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = C * (‖fun i => w i x‖ * ν) ^ k := by ring
    _ ≤ _ := by gcongr

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspFormOfIntegralOverCuspForms

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem cuspForm_of_integral_over_cuspForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ (la : Wt X.Ψ r) (N k m : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (cf : ℕ → MvPolynomial (Fin N) ℂ) (g : Frame X.Ψ r → ℂ), (∀ i, w i ∈ X.SS la) → 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → X.IsSec (k • la) g → (∀ x ∈ X.dom, g x * g x ^ m + ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i = 0) → g ∈ X.SS (k • la) := by
  intro E _ _ _ r X la N k m w cf g hw hk hcf hg heq
  have hb : X.IsBddSec (k • la) g :=
    isBddSec_of_integral E r X la N k m w cf g (fun i => (hw i).1) hcf hg heq
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ :=
    siegelSpaceAlgebra_holds (E := E) r X ((m + 1) • (k • la)) ((m + 1) • (k • la)) 0
  have hterm : ∀ i ∈ Finset.range m,
      (fun x => MvPolynomial.eval (fun s => w s x) (cf i)) * g ^ (i + 1) ∈
        X.SS ((m + 1) • (k • la)) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.1 hi
    have h1 := eval_isHomogeneous_mem_cuspForms E r X la N ((m - i) * k) w (cf i) hw
      (Nat.mul_pos (Nat.sub_pos_of_lt hi') hk) (hcf i hi')
    have h2 := (bddSec_pow_succ_and_constTerm_pow_succ E r X (k • la) g hb i).1
    have h3 := (siegelSpaceAlgebra_holds (E := E) r X (((m - i) * k) • la) ((i + 1) • (k • la)) 0).2.1 _ h1 _ h2
    have e : ((m - i) * k) • la + (i + 1) • (k • la) = (m + 1) • (k • la) := by
      rw [mul_smul, ← add_smul]
      congr 1
      omega
    rwa [e] at h3
  have hsum := Finset.sum_induction _ (fun P => P ∈ X.SS ((m + 1) • (k • la)))
    (fun a b ha hb => hadd a ha b hb) h0 hterm
  have hneg := hsmul (-1) _ hsum
  refine cuspForm_of_bddSec_of_pow_succ E r X (k • la) g m hb
    ((DomCongr.bddSec_cusp_congr E r X _ _ _ fun x hx => ?_).2 hneg)
  have h := heq x hx
  have e : ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i =
      ∑ i ∈ Finset.range m, MvPolynomial.eval (fun s => w s x) (cf i) * g x ^ (i + 1) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h
  simp only [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  linear_combination -h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCuspFormOfIntegralOverDominantWeight

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory


open IntegralCusp in
theorem cusp_of_integral_of_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), AllTest Xo c → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → ∀ g ∈ sec Xo c (k • a) (k * n), g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 → g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n) := by
  intro E _ _ _ H Dw l Xo c hT r U hU a n N w hD hw k m cf hk hcf g hg heq
  unfold Formalism.L2.PjFree.cusp
  refine ⟨hg, ?_⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
  intro σ hσ
  unfold Formalism.L2.PjFree.holSub
  refine Submodule.subset_span ?_
  show Formalism.L2.PjFree.IsHolCusp _ _ _
  unfold Formalism.L2.PjFree.IsHolCusp
  intro j
  have hDk : Dom (k • a) (k * n) := by
    unfold Dom at hD ⊢
    refine ⟨fun τ i i' hii' => ?_, hD.2.mul_left k⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Nat.mul_le_mul_left k (hD.1 τ hii')
  have hla : Formalism.L2.PjFree.laU (U σ) (k • a) (k * n) j = k • Formalism.L2.PjFree.laU (U σ) a n j := by
    funext τ i
    rw [laU_nsmul (U σ) a n k hD.2 j τ i]
    simp [Pi.smul_apply]
  have hsec := (hU σ hσ).2.2.2.2.1 (k • a) (k * n) hDk g hg j
  rw [hla] at hsec ⊢
  have hwS : ∀ s, Formalism.L2.PjFree.rdU (U σ) (w s) j ∈ ((U σ).X j).SS (Formalism.L2.PjFree.laU (U σ) a n j) := by
    intro s
    have h1 := hw s
    unfold Formalism.L2.PjFree.cusp at h1
    have h2 := h1.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap] at h2
    exact GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (h2 σ hσ) j
  refine cuspForm_of_integral_over_cuspForms E r ((U σ).X j) (Formalism.L2.PjFree.laU (U σ) a n j) N k m
    (fun s => Formalism.L2.PjFree.rdU (U σ) (w s) j) (fun i => MvPolynomial.map σ (cf i))
    (Formalism.L2.PjFree.rdU (U σ) g j) hwS hk (fun i hi => (hcf i hi).map σ) hsec ?_
  intro x hx
  have : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have hy := hT (CAt σ) ((U σ).un j ⟨x, hx⟩)
  have key : ∀ f, Formalism.L2.PjFree.rdU (U σ) f j x = evHom ((U σ).un j ⟨x, hx⟩) hy f := by
    intro f
    unfold Formalism.L2.PjFree.rdU
    simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
    rfl
  simp only [key]
  have h3 := congrArg (evHom ((U σ).un j ⟨x, hx⟩) hy) heq
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_add (f := _), map_mul, map_sum, map_pow, map_zero, evHom_aeval] using h3

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCuspFormOfIntegralOverDominantWeightStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.isCuspForm_of_integral_over_dominantWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), AllTest Xo c → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → ∀ g ∈ sec Xo c (k • a) (k * n), g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 → g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n) := by
  first | exact @GlobalTheory.cusp_of_integral_of_dom | exact GlobalTheory.cusp_of_integral_of_dom | (intros; apply GlobalTheory.cusp_of_integral_of_dom <;> assumption)
end
end
